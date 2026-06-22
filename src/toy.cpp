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
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include <cassert>
#include <cstdint>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <system_error>
#include <utility>
#include <vector>
#include <algorithm>



using namespace llvm;
using namespace llvm::sys;
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
  tok_number = -5,

  // control
  tok_if = -6,
  tok_then = -7,
  tok_else = -8,
  tok_for = -9,
  tok_in = -10,

  //operators
  tok_binary = -11,
  tok_unary = -12,

  //var definition
  tok_var = -13

};

static std::string IdentifierStr;
static double NumVal;

struct SourceLocation {
  int Line;
  int Col;
};
static SourceLocation CurLoc;
static SourceLocation LexLoc = {1,0};

static int advance() {
  int LastChar = getchar();
  if (LastChar == '\n' || LastChar == '\r') {
    LexLoc.Line++;
    LexLoc.Col = 0;
  }
  else {
    LexLoc.Col++;
  }
  return LastChar;
}

//for next token
static int gettok() {
  static int LastChar = ' ';

 //skipping whitespaces
  while (isspace(LastChar))
    //LastChar = getchar();
    LastChar = advance();

  CurLoc = LexLoc;

  if (isalpha(LastChar)) { //[a-zA-Z][a-zA-Z0-9]*
    IdentifierStr = LastChar;
    //while (isalnum((LastChar = getchar())))
    while (isalnum((LastChar = advance())))
      IdentifierStr += LastChar;

    if (IdentifierStr == "def")
      return tok_def;
    if (IdentifierStr == "extern")
      return tok_extern;
    if (IdentifierStr == "if")
      return tok_if;
    if (IdentifierStr == "then")
      return tok_then;
    if (IdentifierStr == "else")
      return tok_else;
    if (IdentifierStr == "for")
      return tok_for;
    if (IdentifierStr == "in")
      return tok_in;
    if (IdentifierStr == "binary")
      return tok_binary;
    if (IdentifierStr == "unary")
      return tok_unary;
    if (IdentifierStr == "var")
      return tok_var;
    return tok_identifier;
  }

  if (isdigit(LastChar) || LastChar == '.') {
    std::string NumStr;
    do {
      NumStr += LastChar;
      //LastChar = getchar();
      LastChar = advance();
    } while (isdigit(LastChar) || LastChar == '.');

    NumVal = strtod(NumStr.c_str(), nullptr);
    return tok_number;
  }

  if (LastChar == '#') {
    // # is for comments
    do
      //LastChar = getchar();
      LastChar = advance();
    while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

    if (LastChar != EOF)
      return gettok();
  }

  // file end?
  if (LastChar == EOF)
    return tok_eof;

  int ThisChar = LastChar;
  //LastChar = getchar();
  LastChar = advance();
  return ThisChar;
}

//AST

namespace {
//Base class for all expression nodes.
class ExprAST {
  SourceLocation Loc;
public:
  ExprAST(SourceLocation Loc = CurLoc) : Loc(Loc) {}
  virtual ~ExprAST() = default;
  virtual Value *codegen() = 0;
    //emit IR for the AST node along w. all it depends on, to return an LLVM Value obj.
    //Value: class to represent an SSA register/value in LLVM
  int getLine() const { return Loc.Line; }
  int getCol() const { return Loc.Col; }
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
  VariableExprAST(SourceLocation Loc, const std::string &Name) : ExprAST(Loc), Name(Name) {}
  Value *codegen() override;
  const std::string &getName() const { return Name; }
};

//Expression class for var/in
class VarExprAST : public ExprAST {
  std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;
  std::unique_ptr<ExprAST> Body;

  public:
  VarExprAST(std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames, std::unique_ptr<ExprAST> Body) : VarNames(std::move(VarNames)), Body(std::move(Body)) {}
  Value *codegen() override;
};

//Expression class for binary operators
class BinaryExprAST : public ExprAST {
  char Op;
  std::unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(SourceLocation Loc, char Op, std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
      : ExprAST(Loc), Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
  Value *codegen() override;
};

class UnaryExprAST : public ExprAST {
  char Opcode;
  std::unique_ptr<ExprAST> Operand;

public:
  UnaryExprAST(char Opcode, std::unique_ptr<ExprAST> Operand) : Opcode(Opcode), Operand(std::move(Operand)) {}

  Value *codegen() override;
};

//Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  CallExprAST(SourceLocation Loc, const std::string &Callee,
              std::vector<std::unique_ptr<ExprAST>> Args)
      : ExprAST(Loc), Callee(Callee), Args(std::move(Args)) {}
  Value *codegen() override;
};

//For function prototypes
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;
  bool IsOperator;
  unsigned Precedence; //given precedence if it's a binary op.
  int Line;

public:
  PrototypeAST(SourceLocation Loc, const std::string &Name, std::vector<std::string> Args, bool IsOperator = false, unsigned Prec = 0)
      : Name(Name), Args(std::move(Args)), IsOperator(IsOperator), Precedence(Prec), Line(Loc.Line) {}
  int getLine() const { return Line; }
  Function *codegen();
  const std::string &getName() const { return Name; }

  bool isUnaryOp() const { return IsOperator && Args.size() == 1; }
  bool isBinaryOp() const { return IsOperator && Args.size() == 2; }

  char getOperatorName() const {
    assert(isUnaryOp() || isBinaryOp());
    return Name[Name.size() - 1];
  }

  unsigned getBinaryPrecedence() const { return Precedence; }

  //!EXTRA!
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
  const std::string &getName() const { return Proto->getName(); } //to seek a FunctionAST's name directly, without having to reach through the prototype.
};

//Expression class for if/then/else.
class IfExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, Then, Else;
public:
  IfExprAST(SourceLocation Loc, std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then, std::unique_ptr<ExprAST> Else) : ExprAST(Loc), Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}
  Value *codegen() override;
};

//expression class for 'for' and 'in'
class ForExprAST : public ExprAST {
  std::string VarName;
  std::unique_ptr<ExprAST> Start, End, Step, Body;

public: ForExprAST(const std::string &VarName, std::unique_ptr<ExprAST> Start, std::unique_ptr<ExprAST> End, std::unique_ptr<ExprAST> Step, std::unique_ptr<ExprAST> Body): VarName(VarName), Start(std::move(Start)), End(std::move(End)), Step(std::move(Step)), Body(std::move(Body)) {}
  Value *codegen() override;
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

static std::unique_ptr<ExprAST> ParseVarExpr() {
  getNextToken();
  std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;

  if (CurTok != tok_identifier)
    return LogError("expected identifier after var");

  while (true) {
    std::string Name = IdentifierStr;
    getNextToken();

    std::unique_ptr<ExprAST> Init = nullptr;
    if (CurTok == '=') {
      getNextToken();

      Init = ParseExpression();
      if (!Init) return nullptr;
    }

    VarNames.push_back(std::make_pair(Name, std::move(Init)));

    if (CurTok != ',') break;
    getNextToken();

    if (CurTok != tok_identifier)
      return LogError("Expected identifier list after var");
  }

  if (CurTok != tok_in)
    return LogError("expected 'in' keyword after 'var'");
  getNextToken();

  auto Body = ParseExpression();

  if (!Body)
    return nullptr;

  return std::make_unique<VarExprAST>(std::move(VarNames), std::move(Body));
}

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
  SourceLocation LitLoc = CurLoc;
  getNextToken();

  if (CurTok != '(')
    return std::make_unique<VariableExprAST>(LitLoc, IdName);

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

  return std::make_unique<CallExprAST>(LitLoc, IdName, std::move(Args));
}

//parsing if-then-else expressions
static std::unique_ptr<ExprAST> ParseIfExpr() {
  SourceLocation IfLoc = CurLoc;
  getNextToken(); //consuming 'if'

  auto Cond = ParseExpression();
  if (!Cond)
    return nullptr;

  if (CurTok != tok_then)
    return LogError("The keyword 'then' is expected.");
  getNextToken(); //consuming 'then'

  auto Then = ParseExpression();
  if (!Then)
    return nullptr;

  if (CurTok != tok_else)
    return LogError("They keyword 'else' is expected.");
  getNextToken();

  auto Else = ParseExpression();
  if (!Else)
    return nullptr;

  return std::make_unique<IfExprAST>(IfLoc, std::move(Cond), std::move(Then), std::move(Else));
}

//parsing for expressions
static std::unique_ptr<ExprAST> ParseForExpr() {
  getNextToken();

  if (CurTok != tok_identifier)
    return LogError("An identifier is expected after 'for'");

  std::string IdName = IdentifierStr;
  getNextToken();

  if (CurTok != '=')
    return LogError("A '=' is expected after 'for.'");
  getNextToken();

  auto Start = ParseExpression();
  if (!Start)
    return nullptr;
  if (CurTok != ',')
    return LogError("A ',' is expected after the 'for' start value.");
  getNextToken();

  auto End = ParseExpression();
  if (!End)
    return nullptr;

  //step value is optional
  std::unique_ptr<ExprAST> Step;
  if (CurTok == ',') {
    getNextToken();
    Step = ParseExpression();
    if (!Step)
      return nullptr;
  }

  if (CurTok != tok_in)
    return LogError("An 'in' is expected after 'for'");
  getNextToken();

  auto Body = ParseExpression();
  if (!Body)
    return nullptr;

  return std::make_unique<ForExprAST>(IdName, std::move(Start), std::move(End), std::move(Step), std::move(Body));
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
  case tok_if:
    return ParseIfExpr();
  case tok_for:
    return ParseForExpr();
  case tok_var:
    return ParseVarExpr();
  }
}

static std::unique_ptr<ExprAST> ParseUnary() {
  if (!isascii(CurTok) || CurTok == '(' || CurTok == ',')
    return ParsePrimary();

  int Opc = CurTok;
  getNextToken();
  if (auto Operand = ParseUnary())
    return std::make_unique<UnaryExprAST>(Opc, std::move(Operand));
  return nullptr;
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
    SourceLocation BinLoc = CurLoc;
    getNextToken();

    // parsing the RHS
    //auto RHS = ParsePrimary();
    auto RHS = ParseUnary();
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
        std::make_unique<BinaryExprAST>(BinLoc, BinOp, std::move(LHS), std::move(RHS));
  }
}

//primary binary operator RHS
static std::unique_ptr<ExprAST> ParseExpression() {
  //auto LHS = ParsePrimary();
  auto LHS = ParseUnary();
  if (!LHS)
    return nullptr;

  return ParseBinOpRHS(0, std::move(LHS));
}

//function prototype
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  SourceLocation FnLoc = CurLoc;
  std::string FnName;

  unsigned Kind = 0; //0: identifier, 1: unary, 2: binary
  unsigned BinaryPrecedence = 30;

  switch (CurTok) {
    default:
      return LogErrorP("Expected function name in prototype");
    case tok_identifier:
      FnName = IdentifierStr;
      Kind = 0;
      getNextToken();
      break;
    case tok_unary:
      getNextToken();
      if (!isascii(CurTok))
        return LogErrorP("Expected unary operator.");
      FnName = "unary";
      FnName += (char)CurTok;
      Kind = 1;
      getNextToken();
      break;
    case tok_binary:
      getNextToken();
      if (!isascii(CurTok))
        return LogErrorP("Expected binary operator.");
      FnName = "binary";
      FnName += (char)CurTok;
      Kind = 2;
      getNextToken();

      //Read the precedence if present.
      if (CurTok == tok_number) {
        if (NumVal < 1 || NumVal > 100)
          return LogErrorP("Invalid precedence: must be 1..100");
        BinaryPrecedence = (unsigned)NumVal;
        getNextToken();
      }
      break;
  }

  if (CurTok != '(')
    return LogErrorP("Expected '(' in prototype");

  std::vector<std::string> ArgNames;

  while (getNextToken() == tok_identifier)
    ArgNames.push_back(IdentifierStr);
  if (CurTok != ')')
    return LogErrorP("Expected ')' in prototype");

  getNextToken();

  if (Kind && ArgNames.size() != Kind)
    return LogErrorP("Invalid number of operands for operator.");

  return std::make_unique<PrototypeAST>(FnLoc, FnName, std::move(ArgNames), Kind != 0, BinaryPrecedence);
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
  SourceLocation FnLoc = CurLoc;
  if (auto E = ParseExpression()) {
    //auto Proto = std::make_unique<PrototypeAST>("__anon_expr", std::vector<std::string>());
    auto Proto = std::make_unique<PrototypeAST>(FnLoc, "main",
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
//static std::map<std::string, Value *> NamedValues; //tracks values defined in current scope and their LLVM representation; symbol table for code
static std::map<std::string, AllocaInst*> NamedValues;
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
static std::unique_ptr<DIBuilder> DBuilder;

struct DebugInfo {
  DICompileUnit *TheCU = nullptr;
  DIType *Db1Ty = nullptr;
  std::vector<DIScope *> LexicalBlocks;

  DIType *getDoubleTy() {
    if (Db1Ty) return Db1Ty;
    Db1Ty = DBuilder->createBasicType("double", 64, dwarf::DW_ATE_float);
    return Db1Ty;
  }

  void emitLocation(ExprAST *AST) {
    if (!AST) {
      Builder->SetCurrentDebugLocation(DebugLoc());
      return;
    }
    DIScope *Scope = LexicalBlocks.empty() ? (DIScope *)TheCU : LexicalBlocks.back();
    Builder->SetCurrentDebugLocation(DILocation::get(Scope->getContext(), AST->getLine(), AST->getCol(), Scope));
  }
} KSDbgInfo;

static DISubroutineType *CreateFunctionType(unsigned NumArgs) {
  SmallVector<Metadata *, 8> EltTys;
  DIType *DblTy = KSDbgInfo.getDoubleTy();
  EltTys.push_back(DblTy);
  for (unsigned i = 0; i < NumArgs; i++)
    EltTys.push_back(DblTy);
  return DBuilder->createSubroutineType(DBuilder->getOrCreateTypeArray(EltTys));

}


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

//Creates an IRBuilder object that points to the first instruction of the entry block.
//Then creates an alloca with the expected name and returns it.
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction, StringRef VarName) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
  return TmpB.CreateAlloca(Type::getDoubleTy(*TheContext), nullptr, VarName);
}

Value *NumberExprAST::codegen() {
  KSDbgInfo.emitLocation(this);
  return ConstantFP::get(*TheContext, APFloat(Val));
  //numeric constants in LLVM are represented with the ConstantFP class
  //holds the numeric val in APFloat internally
  //APFloat holds floating pt constants of random precision
}

// Value *VariableExprAST::codegen() {
//   //Look up the variable in the fxn
//   Value *V = NamedValues[Name];
//   if (!V)
//     return LogErrorV("Unknown variable name.");
//   return V;
//   //merely checks whether the specified name is in the NamedValues map, assuming the variable has already been emitted somewhere with its value available
//   //in practice, only fxn args can be in the NV map
// }

Value *VariableExprAST::codegen() {
  AllocaInst *A = NamedValues[Name];
  if (!A)
    return LogErrorV("Unknown variable name");
  KSDbgInfo.emitLocation(this);
  //Loading the value.
  return Builder->CreateLoad(A->getAllocatedType(), A, Name.c_str());
}

Value *VarExprAST::codegen() {
  std::vector<AllocaInst *> OldBindings;
  Function *TheFunction = Builder->GetInsertBlock()->getParent();
  //Register all variables and emit their initialiser.
  for (unsigned i = 0, e = VarNames.size(); i != e; ++i) {
    const std::string &VarName = VarNames[i].first;
    ExprAST *Init = VarNames[i].second.get();

    Value *InitVal;
    if (Init) {
      InitVal = Init->codegen();
      if (!InitVal)
        return nullptr;
    }
    else {
      InitVal = ConstantFP::get(*TheContext, APFloat(0.0));
    }

    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);
    Builder->CreateStore(InitVal, Alloca);

    OldBindings.push_back(NamedValues[VarName]);
    NamedValues[VarName] = Alloca;
  }

  KSDbgInfo.emitLocation(this);

  Value *BodyVal = Body->codegen();
  if (!BodyVal)
    return nullptr;

  for (unsigned i = 0, e = VarNames.size(); i != e; ++i)
    NamedValues[VarNames[i].first] = OldBindings[i];

  return BodyVal;
}

Value *BinaryExprAST::codegen() {
  KSDbgInfo.emitLocation(this);
  //Special case '=' because we don't want to emit the LHS as an expression.
  if (Op == '=') {
    VariableExprAST *LHSE = static_cast<VariableExprAST*>(LHS.get());
    if (!LHSE)
      return LogErrorV("Destination of '=' must be a variable.");

    Value *Val = RHS->codegen();
    if (!Val)
      return nullptr;

    Value *Variable = NamedValues[LHSE->getName()];
    if (!Variable)
      return LogErrorV("Unknown variable name.");

    Builder->CreateStore(Val, Variable);
    return Val;
  }

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
      //return LogErrorV("invalid binary operator");
      break;

  }

  //If not a built-in binary operator, it's a user defined one. We emit a call to it.
  Function *F = getFunction(std::string("binary") + Op);
  assert(F && "binary operator not found!");

  Value *Ops[2] = { L, R };
  return Builder->CreateCall(F, Ops, "binop");

}

Value *UnaryExprAST::codegen() {
  KSDbgInfo.emitLocation(this);
  Value *OperandV = Operand->codegen();
  if (!OperandV)
    return nullptr;

  Function *F = getFunction(std::string("unary") + Opcode);
  if (!F)
    return LogErrorV("Unknown unary operator");

  return Builder->CreateCall(F, OperandV, "unop");
}

Value *CallExprAST::codegen() {
  KSDbgInfo.emitLocation(this);
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

Value *IfExprAST::codegen() {
  KSDbgInfo.emitLocation(this);
  Value *CondV = Cond->codegen();
  if (!CondV)
    return nullptr;

  //the condition is converted to a boolean to compare a non-equal to 0.0
  CondV = Builder->CreateFCmpONE(CondV, ConstantFP::get(*TheContext, APFloat(0.0)), "ifcond");
  Function *TheFunction = Builder->GetInsertBlock()->getParent();
  BasicBlock *ThenBB = BasicBlock::Create(*TheContext, "then", TheFunction);
  BasicBlock *ElseBB = BasicBlock::Create(*TheContext, "else");
  BasicBlock *MergeBB = BasicBlock::Create(*TheContext, "ifcont");
  Builder->CreateCondBr(CondV, ThenBB, ElseBB);

  //Emitting 'then' value
  Builder->SetInsertPoint(ThenBB);
  Value *ThenV = Then->codegen();

  if (!ThenV)
    return nullptr;

  Builder->CreateBr(MergeBB);
  //'Then's codegen can change the current block, so update ThenBB for the Phi.
  ThenBB = Builder->GetInsertBlock();

  //Emitting the 'else' block
  TheFunction->insert(TheFunction->end(), ElseBB);
  Builder->SetInsertPoint(ElseBB);

  Value *ElseV = Else->codegen();
  if (!ElseV)
    return nullptr;

  Builder->CreateBr(MergeBB);
  //like 'then's codegen changing the current block, else's codegen can too; so update ElseBB for the Phi.
  ElseBB = Builder->GetInsertBlock();

  //Emitting the merge block.
  TheFunction->insert(TheFunction->end(), MergeBB);
  Builder->SetInsertPoint(MergeBB);
  PHINode *PN = Builder->CreatePHI(Type::getDoubleTy(*TheContext), 2, "iftmp");

  PN->addIncoming(ThenV, ThenBB);
  PN->addIncoming(ElseV, ElseBB);
  return PN;
}

Value *ForExprAST::codegen() {
  KSDbgInfo.emitLocation(this);
  //basic block for loop header, inserted after current block
  Function *TheFunction = Builder->GetInsertBlock()->getParent();

  //Creating an alloca for the variable in the entry block.
  AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);

  //Emitting the start code first, without 'variable' in scope.
  Value *StartVal = Start->codegen();
  if (!StartVal)
    return nullptr;

  //Storing the value into the alloca.
  Builder->CreateStore(StartVal, Alloca);
  AllocaInst *OldVal = NamedValues[VarName];
  NamedValues[VarName] = Alloca;

  BasicBlock *LoopBB = BasicBlock::Create(*TheContext, "loop", TheFunction);

  //explicitly specifying the "fall-through" (natural sequence of where to go next), from current block to LoopBB
  Builder->CreateBr(LoopBB);

  //insertion into LoopBB
  Builder->SetInsertPoint(LoopBB);

  //Emitting the loop's body, which can (like o exprs) modify the basic block.
  if (!Body->codegen())
    return nullptr;

  //Emitting the step value
  Value *StepVal = nullptr;
  if (Step) {
    StepVal = Step->codegen();
    if (!StepVal)
      return nullptr;
  }
  else {
    StepVal = ConstantFP::get(*TheContext, APFloat(1.0)); //using 1.0 if not specified
  }

  //Reload, increment, restore alloca. Handles cases where loop's body mutates the variable.
  Value *CurVar = Builder->CreateLoad(Alloca->getAllocatedType(), Alloca, VarName.c_str());
  Value *NextVar = Builder->CreateFAdd(CurVar, StepVal, "nextvar");
  Builder->CreateStore(NextVar, Alloca);

  //Computing the end condition.
  Value *EndCond = End->codegen();
  if (!EndCond)
    return nullptr;

  //Condition is converted to a bool by comparing non-equal to 0.0
  EndCond = Builder->CreateFCmpONE(EndCond, ConstantFP::get(*TheContext, APFloat(0.0)), "loopcond");

  //Creating the "after loop" block and inserting it
  BasicBlock *LoopEndBB = Builder->GetInsertBlock();
  BasicBlock *AfterBB = BasicBlock::Create(*TheContext, "afterloop", TheFunction);

  //Inserting the conditional branch into the end of LoopEndBB
  Builder->CreateCondBr(EndCond, LoopBB, AfterBB);

  //Any new code will be inserted in AfterBB.
  Builder->SetInsertPoint(AfterBB);

  //Restoring the unshadowed variable.
  if (OldVal)
    NamedValues[VarName] = OldVal;
  else
    NamedValues.erase(VarName);

  //a 'for' expression always returns 0.0
  return Constant::getNullValue(Type::getDoubleTy(*TheContext));
}

Function *PrototypeAST::codegen() {
  std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
  FunctionType *FT = FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);

  Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

  unsigned Idx = 0;
  for (auto &Arg : F->args())
    Arg.setName(Args[Idx++]);
  return F;
}


Function *FunctionAST::codegen() { //performs checks for arity, redefinition of existing fxns, etc.
  std::string Name = Proto->getName();
  FunctionProtos[Name] = std::move(Proto);  // Store FIRST

  Function *TheFunction = getFunction(Name);
  if (!TheFunction) return nullptr;

  if (TheFunction->arg_size() != FunctionProtos[Name]->getArgs().size()) {
    return (Function*)LogErrorV("Arity mismatch");
  }

  if (FunctionProtos[Name]->isBinaryOp())
    BinopPrecedence[FunctionProtos[Name]->getOperatorName()] = FunctionProtos[Name]->getBinaryPrecedence();

  // Name args
  unsigned Idx = 0;
  for (auto &Arg : TheFunction->args()) {
    Arg.setName(FunctionProtos[Name]->getArgs()[Idx++]);
  }

  if (!TheFunction->empty())
    return (Function*)LogErrorV("Function cannot be redefined.");

  //Debug Info: Creating the DISubprogram:
  DIFile *Unit = DBuilder->createFile(KSDbgInfo.TheCU->getFilename(), KSDbgInfo.TheCU->getDirectory());
  unsigned Lineno = FunctionProtos[Name]->getLine();
  DISubprogram *SP = DBuilder->createFunction(Unit, Name, StringRef(), Unit, Lineno, CreateFunctionType(TheFunction->arg_size()), Lineno, DINode::FlagPrototyped, DISubprogram::SPFlagDefinition);
  TheFunction->setSubprogram(SP);

  //Pushing the scope to the Lexical Block
  KSDbgInfo.LexicalBlocks.push_back(SP);

  //Supressing debug location for the prologue (alloca setup)
  KSDbgInfo.emitLocation(nullptr);

  // BUILD FUNCTION BODY
  BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
  Builder->SetInsertPoint(BB);
  NamedValues.clear();
  unsigned ArgIdx = 0;
  for (auto &Arg : TheFunction->args()) {
    //Create an alloca for this variable.
    AllocaInst *Alloca =  CreateEntryBlockAlloca(TheFunction, Arg.getName());

    //Debug descriptor for the argument
    DILocalVariable *D = DBuilder->createParameterVariable(SP, Arg.getName(), ++ArgIdx, Unit, Lineno, KSDbgInfo.getDoubleTy(), true);
    DBuilder->insertDeclare(Alloca, D, DBuilder->createExpression(), DILocation::get(SP->getContext(), Lineno, 0, SP), Builder->GetInsertBlock());

    Builder->CreateStore(&Arg, Alloca);
    NamedValues[std::string(Arg.getName())] = Alloca;
  }

  //Emitting the location for the body
  KSDbgInfo.emitLocation(Body.get());

  if (Value *RetVal = Body->codegen()) {
    Builder->CreateRet(RetVal);
    KSDbgInfo.LexicalBlocks.pop_back(); //pop the scope
    verifyFunction(*TheFunction);
    TheFPM->run(*TheFunction, *TheFAM);
    return TheFunction;
  }

  TheFunction->eraseFromParent();
  KSDbgInfo.LexicalBlocks.pop_back(); //popping even on error

  if (FunctionProtos[Name]->isBinaryOp())
    BinopPrecedence.erase(FunctionProtos[Name]->getOperatorName());

  return nullptr;
}


//DISPLAYING WHAT'S BEEN PARSED; JIT DRIVER

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
  //Promote allocas to registers
  //TheFPM->addPass(PromotePass()); //older version
  TheFPM->addPass(PromotePass());
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

static void HandleDefinition() {
  if (auto FnAST = ParseDefinition()) {
    std::string FnName = FnAST->getName();

    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read function definition: ");
      FnIR->print(errs());
      fprintf(stderr, "\n");

      //AOT Emit, before JIT takes over the module
      {
        auto TargetTriple = sys::getDefaultTargetTriple();
        TheModule->setTargetTriple(Triple(TargetTriple));

        std::string Error;
        auto Target = TargetRegistry::lookupTarget(TheModule->getTargetTriple(), Error);
        if (Target) {
          TargetOptions opt;
          auto TM = Target->createTargetMachine(
              Triple(TargetTriple), "generic", "", opt, Reloc::PIC_);
          TheModule->setDataLayout(TM->createDataLayout());

          std::error_code EC;
          raw_fd_ostream dest("output.o", EC, sys::fs::OF_None);
          if (!EC) {
            legacy::PassManager pass;
            TM->addPassesToEmitFile(pass, dest, nullptr, CodeGenFileType::ObjectFile);
            pass.run(*TheModule);
            dest.flush();
            fprintf(stderr, "Wrote output.o\n");
          }
        }
      }

      //Finalising the debug info, as the module still belongs to us here.
      DBuilder->finalize();

      if (FunctionTrackers.count(FnName)) {
        ExitOnErr(FunctionTrackers[FnName]->remove());
        FunctionTrackers.erase(FnName);
      }

      auto RT = TheJIT->getMainJITDylib().createResourceTracker();
      auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
      ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
      FunctionTrackers[FnName] = RT;

      InitialiseModuleAndManagers();

      //Rebuild DBuilder + compile unit for the fresh module.
      DBuilder = std::make_unique<DIBuilder>(*TheModule);
      KSDbgInfo.TheCU = DBuilder->createCompileUnit(dwarf::DW_LANG_C, DBuilder->createFile("test.k", "."), "Kaleidoscope Compiler", false, "", 0);
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

//NORMAL
// static void HandleTopLevelExpression() {
//   if (auto FnAST = ParseTopLevelExpr()) {
//     if (auto *FnIR = FnAST->codegen()) {
//       fprintf(stderr, "Read top-level expression:\n");
//       FnIR->print(errs());
//       fprintf(stderr, "\n");

//       // Use resource tracker for module lifetime control
//       auto RT = TheJIT->getMainJITDylib().createResourceTracker();

//       // Move current module/context to JIT
//       auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
//       ExitOnErr(TheJIT->addModule(std::move(TSM), RT));

//       // Reset for next expression
//       InitialiseModuleAndManagers();

//       // Lookup & execute - LLVM 21/KaleidoscopeJIT compatible
//       auto ExprSymbol = TheJIT->lookup("__anon_expr");
//       if (ExprSymbol) {
//         uintptr_t Addr = ExprSymbol->getAddress().getValue();
//         double (*FP)() = reinterpret_cast<double(*)()>(Addr);
//         fprintf(stderr, "Evaluated to %f\n", FP());
//       } else {
//         fprintf(stderr, "JIT lookup failed for __anon_expr\n");
//       }

//       // Cleanup JIT memory
//       ExitOnErr(RT->remove());
//     }
//   } else {
//     getNextToken();  // Skip bad input
//   }
// }

//DEBUGGING
static void HandleTopLevelExpression() {
  if (auto FnAST = ParseTopLevelExpr()) {
    if (auto *FnIR = FnAST->codegen()) {
      //Allow generated IR to dump to stderr. No more JIT.
      fprintf(stderr, "Read top-level expression:\n");
      FnIR->print(errs());
      fprintf(stderr, "\n");
    }
    else {
      //Skip the  token for error recovery.
      getNextToken();
    }
  }
}

//MAIN

static void MainLoop() {
  while (true) {
    //fprintf(stderr, "ready> ");
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
  InitializeAllTargetInfos();
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmParsers();
  InitializeAllAsmPrinters();

  BinopPrecedence['='] = 2;
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40;

  //fprintf(stderr, "ready> ");
  getNextToken();

  TheJIT = ExitOnErr(KaleidoscopeJIT::Create());
  InitialiseModuleAndManagers();

  //DWARF version we're using.
  TheModule->addModuleFlag(Module::Warning, "Debug Info Version", DEBUG_METADATA_VERSION);

  //macOS supports Dwarf 2.
  if (Triple(sys::getDefaultTargetTriple()).isOSDarwin())
    TheModule->addModuleFlag(Module::Warning, "Dwarf Version", 2);

  //DBuilder
  DBuilder = std::make_unique<DIBuilder>(*TheModule);

  //Compile unit creation.
  KSDbgInfo.TheCU = DBuilder->createCompileUnit(dwarf::DW_LANG_C, DBuilder->createFile("test.k", "."), "Kaleidoscope Compiler", false, "", 0);

  // DBuilder->finalize();
  // TheModule->print(errs(), nullptr);

  MainLoop();

  return 0;
}
