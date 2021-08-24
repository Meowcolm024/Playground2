#include <iostream>
#include <variant>
#include <string>

std::variant<int, std::string> safe_div(int x, int y) {
    std::variant<int, std::string> tmp;
    if (y == 0)
        tmp = "Div by zero!";
    else
        tmp = x / y;
    return tmp;
}

int main() {
    auto x = safe_div(15, 5);
    auto y = safe_div(3, 0);
    if (std::holds_alternative<int>(x))
        std::cout << std::get<int>(x) << std::endl;
    else
        std::cout << std::get<std::string>(x) << std::endl;
    
    if (std::holds_alternative<int>(y))
        std::cout << std::get<int>(y) << std::endl;
    else
        std::cout << std::get<std::string>(y) << std::endl;

    return 0;
}