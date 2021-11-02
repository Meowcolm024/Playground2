#include <iostream>

int main() {

    auto i = new int(233);

    std::cout << "This program leaks memory!\n";

    // delete i;

    return 0;
}