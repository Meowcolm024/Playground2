
int f(const float arr[3])
{
    // arr is still pointer!
}

int g(const float arr[])
{
}

class C
{
    int x;
    int y;
    float z;
    C() = default;
    C(int a, int b) : x(a), y(b) {}
    C(const int arr[2]) { *this = arr; }    // recursion! implicit type conversion
};