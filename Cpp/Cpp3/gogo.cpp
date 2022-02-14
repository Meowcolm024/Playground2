#include <iostream>
#include <array>
// #include <memory>
using namespace std;

int fact(int s)
{
    int acc = 1;
FAC:
    if (s > 0)
    {
        acc *= s;
        s -= 1;
        goto FAC;
    }
    return acc;
}

int main()
{
    string buffer;
    cin >> buffer;

    cout << stoi(buffer) << endl;

    int i = 10;
    while (i-- > 0)
    {
        cout << i << endl;
    }

    auto xs = array<int, 5>{1, 2, 3, 4, 5};
    for (auto x : xs)
        cout << x << " ";
    cout << endl;

    cout << (-17) % (-5) << " " << 17 % (-5) << endl;

    int j = 0;
    for (; j < 10; j++)
    {
    }

    int x = 10;
    cout << x++ + 10 + x++ << endl;
    // 10; => x = 11
    // 10;
    // 11; => x = 12

    if (x = 5) {
        cout << x << endl;
    }

    decltype(x = 5) z;

    return 0;
}