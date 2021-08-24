#include <iostream>
using namespace std;

void hi(int*& a) {
    cout << *a << endl;
}

int main() {
    int *a = new int(10);
    hi(a);
    delete a;
    return 0;
}