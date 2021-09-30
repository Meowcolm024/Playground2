#include <iostream>
using namespace std;

int main() {
    auto x = new int(2);
    cout << x << endl;
    delete x;
    
    auto y = new int(3);
    cout << y << endl;
    delete y;
    
    // ! DANGEROUS
    *y = 100;
    auto z = new int;
    cout << *z << endl;
    delete z;

    return 0;
}
