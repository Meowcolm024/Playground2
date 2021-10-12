#include <iostream>
using namespace std;

int main()
{
    char buffer[4][16] = {};

    cout << "Start:" << endl;
    for (auto &l : buffer)
    {
        cin.getline(l, 16);
        cin.clear();
    }

    cout << "Output:" << endl;
    for (auto &l : buffer)
    {
        for (auto b : l)
            cout << b;
        cout << endl;
    }

    return 0;
}