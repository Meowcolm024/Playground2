#include <iostream>

template <typename T>
class Rc
{
private:
    T *ptr;
    unsigned int *count;

public:
    Rc() : ptr(nullptr), count(nullptr) {}

    Rc(T *p) : ptr(p)
    {
        count = new unsigned int(1);
    }

    Rc(const Rc<T> &r)
    {
        ptr = r.ptr;
        count = r.count;
        (*count)++;
    }

    Rc(Rc<T> &&r)
    {
        ptr = std::move(r.ptr);
        count = r.count;
        
        r.ptr = nullptr;
        r.count = nullptr;
    }

    ~Rc()
    {
        if (count != nullptr)
        {
            (*count)--;
            if (*count == 0)
            {
                delete ptr;
                ptr = nullptr;
                delete count;
                count = nullptr;
            }
        }
    }

    Rc<T> &operator=(const Rc<T> &r)
    {
        if (&r == this)
            return *this;

        if (count != nullptr)
        {
            (*count)--;
            if (*count == 0)
            {
                delete ptr;
                ptr = nullptr;
                delete count;
                count = nullptr;
            }
        }

        ptr = r.ptr;
        count = r.count;
        (*count)++;

        return *this;
    }

    Rc<T> &&operator=(Rc<T> &&r)
    {
        if (count != nullptr)
        {
            (*count)--;
            if (*count == 0)
            {
                delete ptr;
                ptr = nullptr;
                delete count;
                count = nullptr;
            }
        }

        ptr = r.ptr;
        count = r.count;
        r.ptr = nullptr;
        r.count = nullptr;

        return *this;
    }

    T &operator*() {
        return *ptr;    // notice nullptr
    }

    T* get() {
        return ptr;
    }

    const T* get() const {
        return ptr;
    }

    std::string debug() const
    {
        if (!count)
            return "<Deleted ptr>";
        else
            return "Counted: " + std::to_string(*count);
    }
};

void addOne(Rc<int> i) {
    (*i)++;
    std::cout << i.debug() << std::endl;
}

int main()
{
    using namespace std;

    auto p1 = Rc<int>(new int(233));
    auto p2 = p1;
    auto p3 = move(p2);
    p3 = p3;

    cout << p1.debug() << endl;
    cout << p2.debug() << endl;

    addOne(p1);
    cout << *p3 << endl;

    return 0;
}