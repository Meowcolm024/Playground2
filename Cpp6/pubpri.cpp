#include <iostream>
#include <typeinfo>
using namespace std;

class Aturoria
{
public:
    virtual void f() { cout << "hi\n"; }
};

class Merlin : public Aturoria
{
private:
    virtual void f() override { cout << "bye\n"; }
};

struct Okita {
    void f() {cout << "hello\n";}
};

struct Asagami: public Okita {

};

int main()
{
    auto a = new Aturoria();
    Aturoria *b = new Merlin();
    a->f();
    // ! call private method using virtual functions !
    b->f();

    // check type
    cout << typeid(*a).name() << "\n"
         << typeid(*b).name() << endl;

    Okita* c = new Asagami();

    // no virtual, treat as type points to
    cout << typeid(*c).name() << endl;

    delete a;
    delete b;
    delete c;
    return 0;
}