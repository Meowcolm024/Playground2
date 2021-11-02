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
};

class C : public B
{
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
    hiiiiiiiiiiii(d);
    return 0;
}