#include <iostream>
using namespace std;

class A
{
private:
    char a = 'A';
    char *b;
    friend class D;

public:
    A() : b(new char('b')) {}

    // * memory leak when destructor is not virtual
    virtual ~A()
    {
        cout << "bye A" << endl;
        delete b;
    };

    virtual void hi()
    {
        cout << "hi from " << a << endl;
    }
};

class B : public A
{
public:
    B() : A() {}
    virtual ~B() { cout << "BBB" << endl; };
    virtual void hi() override
    {
        A::hi();
        cout << "tu tu ru" << endl;
    }
};

class C : public B
{
public:
    C() : B() {}
    virtual ~C() { cout << "bye C" << endl; };
    virtual void hi() override
    {
        cout << "omg!" << endl;
    }
};

class D : public A
{
private:
    char *d;

public:
    D() : A(), d(new char('d')) {}

    virtual ~D()
    {
        cout << "bye D" << endl;
        delete d;
    }

    virtual void hi() override
    {
        A::hi();
        A::a = 'D';
        A::hi();
        A::a = 'A';
    }
};

void hiiiiiiiiiiii(A *a)
{
    for (auto i = 0; i < 10; i++)
        a->hi();

    delete a;
    a = nullptr;
}

int main()
{
    auto d = new D();
    hiiiiiiiiiiii(move(d));

    A *c = new C();
    c->hi();
    dynamic_cast<B *>(c)->B::hi();
    delete c;

    return 0;
}