#include <iostream>

using namespace std;

struct A
{
    A() { cout << "A" << endl; }
    ~A() { cout << "-A" << endl; }
};

struct B
{
    B() { cout << "B" << endl; }
    ~B() { cout << "-B" << endl; }
};

struct C
{
    static A a;
    static B b;
    C() { cout << "C" << endl; }
    ~C() { cout << "-C" << endl; }
};

A C::a = A{};
B C::b = B{};

int main()
{
    C c{};
    return 0;
}