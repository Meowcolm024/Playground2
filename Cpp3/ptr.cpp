#include <iostream>
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
    while (i-- > 0) {
        cout << i << endl;
    }

    return 0;
}