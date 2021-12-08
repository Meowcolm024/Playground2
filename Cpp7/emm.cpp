#include <iostream>
using namespace std;

struct S {
     int a;
    int* p;
};

int main() {

    auto x = S {10, new int[3]()};

    S z, y;
    z = y = x;

    double p = 10.0;
    const int& q = p;
    int&& w = p;
    p += 3.14;
    const int& u = w;   // same type as w

    w += 1;

    cout << q << endl;
    cout << w << endl;
    cout << u << endl;
    cout << p << endl;
    
    return 0;
}