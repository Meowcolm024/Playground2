#include <iostream>
using namespace std;
class A
{
public:
    A() { cout << "A" << endl; }
    A(int a) { cout << "Conv A" << endl; }
    A(const A &a) { cout << "Copy A" << endl; }
    virtual ~A() { cout << " ̃A" << endl; }
};
class B : public A
{
public:
    B() { cout << "B" << endl; }
    B(const B &b) : A(b) { cout << "Copy B" << endl; }
    ~B() { cout << " ̃B" << endl; }
};
class C
{
    static A a;
    static B b;

public:
    C() { cout << "C" << endl; }
    C(int c) { cout << "Conv C" << endl; }
    C(const C &c) { cout << "Copy C" << endl; }
    virtual ~C() { cout << " ̃C" << endl; }
};
A obj(20);
A C::a(obj);
class D : public C
{
private:
    B b;
    A **a = new A *[2]
    { new A(b), new B(b) };

public:
    D() { cout << "D" << endl; }
    D(int d) { cout << "Conv D" << endl; }
    D(const D &d) { cout << "Copy D" << endl; }
    ~D()
    {
        cout << " ̃D" << endl;
        for (int i = 1; i >= 0; i--)
            delete a[i];
        delete[] a;
    }
};
void process(const A aObj, const C cObj) { cout << "Processed" << endl; }

int main()
{
    cout << "--- Block 1 ---" << endl;
    C cObj(D(10));
    cout << "--- Block 2 ---" << endl;
    process(10, 20);
    cout << "--- Block 3 ---" << endl;
    D dObj;
    cout << "--- Block 4 ---" << endl;
}
