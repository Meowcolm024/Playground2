#include <iostream>
#include <algorithm>
using namespace std;

template <size_t N>
auto last(const int (&xs)[N]) -> const int &
{
    return xs[N - 1];
}

template <size_t N>
auto corner(const int (&xs)[N][N])
{
    cout << xs[0][0] << endl;
}

template <size_t N>
auto corner2(const int xs[][N])
{
    cout << xs[0][0] << endl;
}

int main()
{
    int a[] = {1, 2, 3};
    cout << last<3>(a) << endl;

    int b[2][2] = {{1, 2}, {3, 4}};

    corner(b);
    corner2(b);

    return 0;
}