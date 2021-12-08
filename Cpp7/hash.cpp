#include <iostream>
#include <vector>
#include <functional>
#include <optional>
using namespace std;

bool isPrime(int n)
{
    bool prime = true;
    for (int i = 2; i <= n / 2; ++i)
    {
        if (n % i == 0)
        {
            prime = false;
            break;
        }
    }
    return prime;
}
int nextPrime(int n)
{
    while (!isPrime(++n))
        ;
    return n;
}

enum class Flag
{
    EMPTY,
    DELETED,
    ACTIVE
};

template <class Key, class T>
struct Cell
{
    optional<Key> key;
    shared_ptr<T> data;
    Flag flag;
    Cell() : data(nullptr), flag(Flag::EMPTY), key(nullopt) {}
};

template <class Key, class T>
class Table
{
private:
    vector<Cell<Key, T>> table;
    int capacity;
    int size;
    function<int(Key, int)> hashFunc;
    function<int(Key, int)> offFunc;

    int getSize() const { return size; }
    // Function to check if the hash table is empty
    bool isEmpty() const { return size == 0; }
    // Function to check if the hash table is half-full
    bool isHalfFull() const { return size > (capacity / 2); }

public:
    Table(int c, function<int(Key, int)> hf, function<int(Key, int)> of) : capacity(c), hashFunc(hf), offFunc(of), size(0)
    {
        table = vector<Cell<Key, T>>(c);
    }

    ~Table() = default;

    optional<int> search(const Key key, int &next) const
    {
        for (auto i = 0; i < capacity - 1; i++)
        {
            auto idx = (hashFunc(key, capacity) + offFunc(key, i)) % capacity;
            const Cell<Key, T> &cell = table[idx];
            next = idx;
            if (cell.flag == Flag::EMPTY)
            {
                return nullopt;
            }
            if (cell.key == key)
            {
                if (cell.flag == Flag::DELETED)
                {
                    return nullopt;
                }
                return idx;
            }
        }
        return nullopt;
    }

    Table &insert(Key key, T data)
    {
        return insert(key, make_shared<T>(data));
    }

    Table &insert(Key key, shared_ptr<T> data)
    {
        if (isHalfFull())
        {
            rehashing();
        }

        int n = 0;
        auto i = search(key, n);
        Cell<Key, T> &cell = table[n];
        cell.data = data;
        if (i == nullopt)
        {
            cell.flag = Flag::ACTIVE;
            cell.key = key;
            size += 1;
        }

        return *this;
    }

    Table &remove(Key key)
    {
        int n = 0;
        auto i = search(key, n);
        if (i)
        {
            table[i.value()].flag = Flag::DELETED;
        }
        size -= 1;
        return *this;
    }

    void rehashing()
    {
        cout << "*** rehashing" << endl;
        vector<Cell<Key, T>> tmp = move(this->table);
        auto p = nextPrime(capacity * 2);
        capacity = p;
        size = 0;
        this->table = vector<Cell<Key, T>>(p);
        for (Cell<Key, T> &cell : tmp)
        {
            if (cell.flag == Flag::ACTIVE)
            {
                insert(cell.key.value(), cell.data);
            }
        }
    }

    void print() const
    {
        cout << "----------\n";
        for (const Cell<Key, T> &cell : table)
        {
            if (cell.flag == Flag::ACTIVE)
            {
                cout << cell.key.value() << " -> " << *cell.data << endl;
            }
        }
        cout << "----------\n";
    }
};

int main()
{
    auto table = Table<int, string>(
        3, [](int key, int capacity)
        { return key % capacity; },
        [](int key, int i)
        { return i * i * i; });

    table.insert(1, "hello").insert(9, "bye").print();
    table.insert(6, "omg").insert(123, "hahah").insert(89, "qwq").print();
    table.insert(1, "bbbbb").remove(89).print();
    table.insert(89, "qwq").insert(56, "hahah").insert(123, "tmd").print();
    table.remove(1).remove(9).print();

    return 0;
}