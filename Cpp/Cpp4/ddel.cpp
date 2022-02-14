#include <iostream>
using namespace std;

int main() {
    auto x = new int(100);
    cout << *x << endl;
    delete x;
    cout << x << endl;
    //auto y = new int;   // recycled!
    delete x;           // double delete?
    return 0;
}

