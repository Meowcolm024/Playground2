#include <iostream>

using namespace std;

void f(const float arr[3])
{
    // arr is still pointer!
    cout << typeid(arr).name() << endl;
}

void g(const float arr[])
{
    cout << typeid(arr).name() << endl;
}

class C
{
    int x;
    int y;
    float z;
    C() = default;
    C(int a, int b) : x(a), y(b) {}
    C(const int arr[2]) { *this = arr; } // ! infinite recursion! implicit type conversion
    // C& opertaor=(const C& x) = delete;
};

int main()
{
    float xs[] = {1, 2, 3};
    f(xs);
    g(xs);

    int x;
    x += 10;
    cout << x << endl;

    return 0;
}
