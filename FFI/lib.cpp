#include <iostream>

int Function(int num) 
{
    std::cout << "Num = " << num << std::endl;
    return 0;
}

extern "C" {
    int MyFunction(int a)
    {
        return Function(a);
    }
}