#include <iostream>
using namespace std;

struct Counter {
    static int count;
    Counter() {
        count++;
    }
    Counter(const Counter &c) {
        count++;
    }
    ~Counter() {
        count--;
    }
    Counter& operator=(Counter c) {
        return *this;
    }
};

int Counter::count = 0;

void check() {
    cout << Counter::count << endl;
}

void copy(Counter c) {check();}
void ref(Counter &c) {check();}
void ptr(Counter *c) {check();}

int main() {
    Counter a = Counter();
    Counter b = Counter();
    Counter* c = new Counter();
    check();
    copy(a);
    ref(b);
    ptr(c);
    check();
    delete c;
    check();
    return 0;
}