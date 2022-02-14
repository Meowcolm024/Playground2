#include <iostream>
using namespace std;

int main()
{
    int x = 10;
    int xs[x];
    for (int i = 0; i < x; i++)
        xs[i] = i;
    cout << xs[x / 2] << endl;
    return 0;
}