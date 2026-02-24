#include "../include/KaleidoscopeJIT.h"
#include "llvm/ExecutionEngine/Orc/SymbolStringPool.h"
using llvm::cantFail;
using llvm::orc::SymbolStringPtr;
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include <cassert>
#include <cstdint>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <algorithm>



using namespace llvm;
using namespace llvm::orc;

//LEXER

// [0-255] returned for unknown characters.
enum Token {
  tok_eof = -1,

  // commands
  tok_def = -2,
  tok_extern = -3,

  // primary
  tok_identifier = -4,
  tok_number = -5
};

static std::string IdentifierStr;
static double NumVal;

//for next token
static int gettok() {
  static int LastChar = ' ';

 //skipping whitespaces
  while (isspace(LastChar))
    LastChar = getchar();

  if (isalpha(LastChar)) { //[a-zA-Z][a-zA-Z0-9]*
    IdentifierStr = LastChar;
    while (isalnum((LastChar = getchar())))
      IdentifierStr += LastChar;

    if (IdentifierStr == "def")
      return tok_def;
    if (IdentifierStr == "extern")
      return tok_extern;
    return tok_identifier;
  }

  if (isdigit(LastChar) || LastChar == '.') {
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = getchar();
    } while (isdigit(LastChar) || LastChar == '.');

    NumVal = strtod(NumStr.c_str(), nullptr);
    return tok_number;
  }

  if (LastChar == '#') {
    // # is for comments
    do
      LastChar = getchar();
    while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

    if (LastChar != EOF)
      return gettok();
  }

  // file end?
  if (LastChar == EOF)
    return tok_eof;

  int ThisChar = LastChar;
  LastChar = getchar();
  return ThisChar;
}

//AST

namespace {
//Base class for all expression nodes.
class ExprAST {
public:
  virtual ~ExprAST() = default;
  virtual Value *codegen() = 0;
    //emit IR for the AST node along w. all it depends on, to return an LLVM Value obj.
    //Value: class to represent an SSA register/value in LLVM
};

//Expression class for numeric literals
class NumberExprAST : public ExprAST {
  double Val;

public:
  NumberExprAST(double Val) : Val(Val) {}
  Value *codegen() override;
};

//Expression class for variables
class VariableExprAST : public ExprAST {
  std::string Name;

public:
  VariableExprAST(const std::string &Name) : Name(Name) {}
  Value *codegen() override;
};

//Expression class for binary operators
class BinaryExprAST : public ExprAST {
  char Op;
  std::unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
      : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
  Value *codegen() override;
};

//Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  CallExprAST(const std::string &Callee,
              std::vector<std::unique_ptr<ExprAST>> Args)
      : Callee(Callee), Args(std::move(Args)) {}
  Value *codegen() override;
};

//For function prototypes
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;

public:
  PrototypeAST(const std::string &Name, std::vector<std::string> Args)
      : Name(Name), Args(std::move(Args)) {}

  Function *codegen();

  const std::string &getName() const { return Name; }

  //getting args so we can compare prototype and definition args
  //even if there's a mismatch, codegen won't be hindered
  //bcs we rename the prototype's args to match the definition's
  const std::vector<std::string> &getArgs() const { return Args; }
};

//function definition
class FunctionAST {
  std::unique_ptr<PrototypeAST> Proto;
  std::unique_ptr<ExprAST> Body;

public:
  FunctionAST(std::unique_ptr<PrototypeAST> Proto,
              std::unique_ptr<ExprAST> Body)
      : Proto(std::move(Proto)), Body(std::move(Body)) {}
  Function *codegen();
  const std::string &getName() const { return Proto->getName(); }
};

}

//PARSER

static int CurTok;
static int getNextToken() { return CurTok = gettok(); } //always eats the token

// precedence for all binary operators
static std::map<char, int> BinopPrecedence;

// precedence of the pending binary operator
static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0)
    return -1;
  return TokPrec;
}

//error handling
std::unique_ptr<ExprAST> LogError(const char *Str) {
  fprintf(stderr, "Error: %s\n", Str);
  return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
  LogError(Str);
  return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression();

//parsing number expressions
static std::unique_ptr<ExprAST> ParseNumberExpr() {
  auto Result = std::make_unique<NumberExprAST>(NumVal);
  getNextToken();
  return std::move(Result);
}

//parsing paranthesis expressions
static std::unique_ptr<ExprAST> ParseParenExpr() {
  getNextToken();
  auto V = ParseExpression();
  if (!V)
    return nullptr;

  if (CurTok != ')')
    return LogError("expected ')'");
  getNextToken();
  return V;
}

//parsing identifier expressions
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
  std::string IdName = IdentifierStr;

  getNextToken();

  if (CurTok != '(')
    return std::make_unique<VariableExprAST>(IdName);

  getNextToken();
  std::vector<std::unique_ptr<ExprAST>> Args;
  if (CurTok != ')') {
    while (true) {
      if (auto Arg = ParseExpression())
        Args.push_back(std::move(Arg));
      else
        return nullptr;

      if (CurTok == ')')
        break;

      if (CurTok != ',')
        return LogError("Expected ')' or ',' in argument list");
      getNextToken();
    }
  }

  getNextToken();

  return std::make_unique<CallExprAST>(IdName, std::move(Args));
}

//primary
static std::unique_ptr<ExprAST> ParsePrimary() {
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_identifier:
    return ParseIdentifierExpr();
  case tok_number:
    return ParseNumberExpr();
  case '(':
    return ParseParenExpr();
  }
}

//binary operator RHS
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS) {
  while (true) {
    int TokPrec = GetTokPrecedence();

    //if current operator's precedence is less than next one's, consume and return the LHS
    if (TokPrec < ExprPrec)
      return LHS;

    int BinOp = CurTok;
    getNextToken();

    // parsing the RHS
    auto RHS = ParsePrimary();
    if (!RHS)
      return nullptr;

    //if the current operator's precedence is greater than/equal to the next one's, merge and consume
    int NextPrec = GetTokPrecedence();
    if (TokPrec < NextPrec) {
      RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
      if (!RHS)
        return nullptr;
    }

    // Merge LHS/RHS.
    LHS =
        std::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
  }
}

//primary binary operator RHS
static std::unique_ptr<ExprAST> ParseExpression() {
  auto LHS = ParsePrimary();
  if (!LHS)
    return nullptr;

  return ParseBinOpRHS(0, std::move(LHS));
}

//function prototype
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  if (CurTok != tok_identifier)
    return LogErrorP("Expected function name in prototype");

  std::string FnName = IdentifierStr;
  getNextToken();

  if (CurTok != '(')
    return LogErrorP("Expected '(' in prototype");

  std::vector<std::string> ArgNames;
  while (getNextToken() == tok_identifier)
    ArgNames.push_back(IdentifierStr);
  if (CurTok != ')')
    return LogErrorP("Expected ')' in prototype");

  getNextToken();

  return std::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}

//function definition
static std::unique_ptr<FunctionAST> ParseDefinition() {
  getNextToken();
  auto Proto = ParsePrototype();
  if (!Proto)
    return nullptr;

  if (auto E = ParseExpression())
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  return nullptr;
}

static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
  if (auto E = ParseExpression()) {
    auto Proto = std::make_unique<PrototypeAST>("__anon_expr",
                                                std::vector<std::string>());
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }
  return nullptr;
}

//extern prototype
static std::unique_ptr<PrototypeAST> ParseExtern() {
  getNextToken();
  return ParsePrototype();
}

//----------
//Code Generation
static std::unique_ptr<LLVMContext> TheContext; //obj owning core LLVM data structures (type, constant value tables)
static std::unique_ptr<IRBuilder<>> Builder; //helper obj to generate LLVM instructions; keeps track of current place to insert instructions and has methods to create new instructions
static std::unique_ptr<Module> TheModule; //contains fxns and globals vars; owns memory for all generated IR
static std::map<std::string, Value *> NamedValues; //tracks values defined in current scope and their LLVM representation; symbol table for code
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::unique_ptr<FunctionPassManager> TheFPM;
static std::unique_ptr<LoopAnalysisManager> TheLAM;
static std::unique_ptr<FunctionAnalysisManager> TheFAM;
static std::unique_ptr<CGSCCAnalysisManager> TheCGAM;
static std::unique_ptr<ModuleAnalysisManager> TheMAM;
static std::unique_ptr<PassInstrumentationCallbacks> ThePIC;
static std::unique_ptr<StandardInstrumentations> TheSI;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;
static std::map<std::string, llvm::orc::ResourceTrackerSP> FunctionTrackers;
static ExitOnError ExitOnErr;


Value *LogErrorV(const char *Str) {
  LogError(Str);
  return nullptr;
}


Function *getFunction(std::string Name) {
  //checking if fxn has already been added to the current module
  if (auto *F = TheModule->getFunction(Name))
    return F;

  auto FI = FunctionProtos.find(Name);
  if (FI != FunctionProtos.end())
    return FI->second->codegen();

  //returning null if no prototype exists
  return nullptr;
}

Value *NumberExprAST::codegen() {
  return ConstantFP::get(*TheContext, APFloat(Val));
  //numeric constants in LLVM are represented with the ConstantFP class
  //holds the numeric val in APFloat internally
  //APFloat holds floating pt constants of random precision
}

Value *VariableExprAST::codegen() {
  //Look up the variable in the fxn
  Value *V = NamedValues[Name];
  if (!V)
    return LogErrorV("Unknown variable name.");
  return V;
  //merely checks whether the specified name is in the NamedValues map, assuming the variable has already been emitted somewhere with its value available
  //in practice, only fxn args can be in the NV map
}

Value *BinaryExprAST::codegen() {
  Value *L = LHS->codegen();
  Value *R = RHS->codegen();
  if (!L || !R)
    return nullptr;

  switch(Op) {
    case '+':
      return Builder->CreateFAdd(L, R, "addtmp");
      //"x_tmp" is to give a name for the newly created instruction
      //if multiple variables are emitted, LLVM automatically provides each one with an increasing, unique numeric suffix
    case '-':
      return Builder->CreateFSub(L, R, "subtmp");
    case '*':
      return Builder->CreateFMul(L, R, "multmp");
    case '<':
      L = Builder->CreateFCmpULT(L, R, "cmptmp");
      //convert a boolean 0 to double 0.0; 1 to 1.0
      return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
    default:
      return LogErrorV("invalid binary operator");
  }
}

Value *CallExprAST::codegen() {
  //looking up call name in the global module table
  Function *CalleeF = getFunction(Callee);
  //Function *CalleeF = TheModule->getFunction(Callee);
  if(!CalleeF)
    return LogErrorV("Unknown function referenced");

  //arg mismatch / arity checking
  if (CalleeF->arg_size() != Args.size())
    return LogErrorV("Incorrect number of arguments passed.");

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    ArgsV.push_back(Args[i]->codegen());
    if (!ArgsV.back())
      return nullptr;
  }
  return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
}

// Function *PrototypeAST::codegen() {
//   //fxn type like: double(double, double) ??
//   std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext)); //creates a vector of 'n' double types
//   FunctionType *FT = FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false); //uses the 'n' double args to give one double result
//   Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get()); //user specified fxn name registered in 'Module' symbol table
//   //returns the LLVM Function, and not the LLVM "Value" computed by the said fxn.

//   unsigned Idx = 0;
//   for (auto &Arg : F->args())
//     Arg.setName(Args[Idx++]);
//   //setting fxn args acc. to. prototype names

//   return F;
// }

Function *PrototypeAST::codegen() {
  std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
  FunctionType *FT = FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);

  Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

  unsigned Idx = 0;
  for (auto &Arg : F->args())
    Arg.setName(Args[Idx++]);
  return F;
}


Function *FunctionAST::codegen() {
  std::string Name = Proto->getName();
  FunctionProtos[Name] = std::move(Proto);  // Store FIRST

  Function *TheFunction = getFunction(Name);
  if (!TheFunction) return nullptr;

  if (TheFunction->arg_size() != FunctionProtos[Name]->getArgs().size()) {
    return (Function*)LogErrorV("Arity mismatch");
  }

  // Name args
  unsigned Idx = 0;
  for (auto &Arg : TheFunction->args()) {
    Arg.setName(FunctionProtos[Name]->getArgs()[Idx++]);
  }

  if (!TheFunction->empty())
    return (Function*)LogErrorV("Function cannot be redefined.");

  // BUILD FUNCTION BODY
  BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
  Builder->SetInsertPoint(BB);
  NamedValues.clear();
  for (auto &Arg : TheFunction->args())
    NamedValues[std::string(Arg.getName())] = &Arg;

  if (Value *RetVal = Body->codegen()) {
    Builder->CreateRet(RetVal);
    verifyFunction(*TheFunction);
    TheFPM->run(*TheFunction, *TheFAM);
    return TheFunction;
  }

  TheFunction->eraseFromParent();
  return nullptr;
}




//DISPLAYING WHAT'S BEEN PARSED; JIT DRIVER

// static void InitialiseModule() {
//   TheContext = std::make_unique<LLVMContext>();
//   TheModule = std::make_unique<Module>("my cool jit", *TheContext);

//   //new builder for the module
//   Builder = std::make_unique<IRBuilder<>>(*TheContext);

// }

void InitialiseModuleAndManagers(void) {
  //New context and module
  TheContext = std::make_unique<LLVMContext>();
  TheModule = std::make_unique<Module>("KaleidoscopeJIT", *TheContext);
  if (TheJIT)
    TheModule->setDataLayout(TheJIT->getDataLayout());
  Builder = std::make_unique<IRBuilder<>>(*TheContext);

  //New builder for the module
  TheFPM = std::make_unique<FunctionPassManager>();
  TheLAM = std::make_unique<LoopAnalysisManager>();
  TheFAM = std::make_unique<FunctionAnalysisManager>();
  TheCGAM = std::make_unique<CGSCCAnalysisManager>();
  TheMAM = std::make_unique<ModuleAnalysisManager>();
  ThePIC = std::make_unique<PassInstrumentationCallbacks>();
  TheSI = std::make_unique<StandardInstrumentations>(*TheContext, /*DebugLogging*/ true);
  TheSI->registerCallbacks(*ThePIC, TheMAM.get());

  //TRANSFORM PASSES
  //Peephole, bit-twiddling optimisations; standard cleanup optimisations useful for wide variety of code
  TheFPM->addPass(InstCombinePass());
  //Reassociate expressions
  TheFPM->addPass(ReassociatePass());
  //Eliminate common subexp
  TheFPM->addPass(GVNPass());
  //Simplify CFG (deleting unreachable blocks, etc.)
  TheFPM->addPass(SimplifyCFGPass());

  //ANALYSIS PASSES for above transform passes
  PassBuilder PB;
  PB.registerModuleAnalyses(*TheMAM);
  PB.registerFunctionAnalyses(*TheFAM);
  PB.crossRegisterProxies(*TheLAM, *TheFAM, *TheCGAM, *TheMAM);

}


// static void HandleDefinition() {
//   if (auto FnAST = ParseDefinition()) {
//     if (auto *FnIR = FnAST->codegen()) {
//       fprintf(stderr, "Read function definition: ");
//       FnIR->print(errs());
//       fprintf(stderr, "\n");
//       ExitOnErr(TheJIT->addModule(ThreadSafeModule(std::move(TheModule), std::move(TheContext))));
//       InitialiseModuleAndManagers();
//     }
//   }
//   else {
//     getNextToken();
//   }
// }

static void HandleDefinition() {
  if (auto FnAST = ParseDefinition()) {
    std::string FnName = FnAST->getName();

    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read function definition: ");
      FnIR->print(errs());
      fprintf(stderr, "\n");

      // Remove old definition if it exists
      if (FunctionTrackers.count(FnName)) {
        ExitOnErr(FunctionTrackers[FnName]->remove());
        FunctionTrackers.erase(FnName);
      }

      // Add new definition with its own tracker
      auto RT = TheJIT->getMainJITDylib().createResourceTracker();
      auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
      ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
      FunctionTrackers[FnName] = RT;  // store for potential future redefinition

      InitialiseModuleAndManagers();
    }
  } else {
    getNextToken();
  }
}



static void HandleExtern() {
  if (auto ProtoAST = ParseExtern()) {
    if (auto *FnIR = ProtoAST->codegen()) {
      fprintf(stderr, "Read extern: ");
      FnIR->print(errs());
      fprintf(stderr, "\n");
      FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
    }
  }
  else {
    getNextToken();
  }
}

// static void HandleTopLevelExpression() {
//   if (auto FnAST = ParseTopLevelExpr()) {
//     if (auto *FnIR = FnAST->codegen()) {
//       fprintf(stderr, "Read top-level expression: ");
//       FnIR->print(errs());
//       fprintf(stderr, "\n");

//       //Remove the anon expression.
//       FnIR->eraseFromParent();
//     }
//   } else {
//     getNextToken();
//   }
// }

static void HandleTopLevelExpression() {
  if (auto FnAST = ParseTopLevelExpr()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read top-level expression:\n");
      FnIR->print(errs());
      fprintf(stderr, "\n");

      // Use resource tracker for module lifetime control
      auto RT = TheJIT->getMainJITDylib().createResourceTracker();

      // Move current module/context to JIT
      auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
      ExitOnErr(TheJIT->addModule(std::move(TSM), RT));

      // Reset for next expression
      InitialiseModuleAndManagers();

      // Lookup & execute - LLVM 21/KaleidoscopeJIT compatible
      auto ExprSymbol = TheJIT->lookup("__anon_expr");
      if (ExprSymbol) {
        uintptr_t Addr = ExprSymbol->getAddress().getValue();
        double (*FP)() = reinterpret_cast<double(*)()>(Addr);
        fprintf(stderr, "Evaluated to %f\n", FP());
      } else {
        fprintf(stderr, "JIT lookup failed for __anon_expr\n");
      }

      // Cleanup JIT memory
      ExitOnErr(RT->remove());
    }
  } else {
    getNextToken();  // Skip bad input
  }
}




//MAIN

static void MainLoop() {
  while (true) {
    fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:
      return;
    case ';':
      //can ignore semicolons
      getNextToken();
      break;
    case tok_def:
      HandleDefinition();
      break;
    case tok_extern:
      HandleExtern();
      break;
    default:
      HandleTopLevelExpression();
      break;
    }
  }
}

int main() {

  InitializeNativeTarget();
  InitializeNativeTargetAsmPrinter();
  InitializeNativeTargetAsmParser();

  //increasing precedence
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40; // highest

  fprintf(stderr, "ready> ");
  getNextToken();

  TheJIT = ExitOnErr(KaleidoscopeJIT::Create());
  InitialiseModuleAndManagers();


  //InitialiseModule();

  //for the interpreter
  MainLoop();

  //TheModule->print(errs(), nullptr);

  return 0;
}
