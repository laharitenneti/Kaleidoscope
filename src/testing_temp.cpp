#include <iostream>

extern "C" {
    double celsius(double fahrenheit) __asm__("_celsius");
}

int main() {
    double f = 68.0;
    double c = celsius(f);
    
    std::cout << f << " degrees Fahrenheit is " << c << " degrees Celsius!" << std::endl;
    return 0;
}