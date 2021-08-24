#include <iostream>

#define NEW(type, ptr) type* ptr = new type;
#define NEWA(type, ptr, len) type* ptr = new type[len];
#define DROP(ptr) delete ptr; ptr = nullptr;
#define DROPA(ptr) delete[] ptr; ptr = nullptr;

using namespace std;

int main()
{
    NEWA(int, test, 10);
    cout << test << endl;
    DROPA(test);
    return 0;
}
