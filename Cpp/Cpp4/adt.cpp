#include <iostream>
#include <any>
using namespace std;

enum class EitherTag
{
    LEFT,
    RIGHT
};

template <class L, class R>
class Either
{
protected:
    Either(EitherTag t) : tag(t) {}
    virtual ~Either() = default;

public:
    const EitherTag tag;
    virtual L &getLeft() = 0;
    virtual R &getRight() = 0;
};

template <class L>
class Left : public Either<L, any>
{
private:
    L value;

public:
    Left(L v) : Either<L, any>(EitherTag::LEFT), value(v) {}
    virtual L &getLeft() override
    {
        return value;
    }
    virtual any &getRight() override {}
};

template <class R>
class Right : public Either<any, R>
{
private:
    R value;

public:
    Right(R v) : Either<any, R>(EitherTag::RIGHT), value(v) {}
    virtual R &getRight() override
    {
        return value;
    }
    virtual any &getLeft() override {}
};

template <class L>
void printOutH(Left<L> *e)
{
    cout << e->getLeft() << endl;
}
template <class R>
void printOutH(Right<R> *e) {
    cout << e->getRight() << endl;
}

template<class L, class R>
void printOut(Either<L, R> *e) {
    if (e->tag == EitherTag::LEFT) {
        printOutH(dynamic_cast<Left<L> * >(e));
    } else {
        printOutH(dynamic_cast<Right<R> * >(e));
    }
}

int main()
{
    auto x = Left<int>(100);
    printOut(&x);
    return 0;
}