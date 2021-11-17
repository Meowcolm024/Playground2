#include <iostream>
#include <sstream>

auto format(const char* f) -> decltype(auto) {
    return std::string(f);
}

template<class T, class ... Ts>
auto format(const char*f, T value, Ts ...rest) -> decltype(auto) {
    auto acc = 0;
    while (f[acc] != '\0' && f[acc] != '%')
        acc++;
    
}

int main() {
    // std::cout << f(1,2,3,4,5) << std::endl;
    return 0;
}