#include <iostream>
#include <vector>
#include <functional>
#include <algorithm>

// ! NOT lazy
template <typename T>
class iter
{
private:
    std::vector<T> content;

public:
    iter(std::vector<T> c) : content(c) {}
    iter(const iter<T> &i) = delete;
    iter(const iter<T> &&i) : content(std::move(i.content)) {}
    ~iter() = default;

    std::vector<T> collect() { return std::move(content); }

    iter<T> &operator=(const iter<T> &i) = delete;
    iter<T> &operator=(const iter<T> &&i)
    {
        content = std::move(i.content);
        return *this;
    }

    template <typename U>
    iter<U> map(std::function<U(T)> f)
    {
        std::transform(content.begin(), content.end(), content.begin(), f);
        return iter(std::move(*this));
    }

    iter<T> filter(std::function<bool(T)> f)
    {
        std::vector<T> tmp{};
        for (auto &i : content)
            if (f(i))
                tmp.push_back(i);
        content = tmp;
        return iter(std::move(*this));
    }

    iter<T> reverse()
    {
        std::vector<T> tmp{};
        for (auto i = content.size(); i > 0; i--)
            tmp.push_back(content[i - 1]);
        content = tmp;
        return iter(std::move(*this));
    }

    // foldl
    template <typename U>
    U fold(U z, std::function<U(U, T)> f)
    {
        for (auto &i : content)
        {
            z = f(z, i);
        }
        return z;
    }

    iter<T> append(const std::vector<T> &xs)
    {
        for (auto &x : xs)
            content.push_back(x);
        return iter(std::move(*this));
    }

    iter<T> drop(size_t n)
    {
        auto x = content.size();
        while (x - n < content.size())
            content.erase(content.begin());
        return iter(std::move(*this));
    }
};

int main()
{
    std::vector<int> xs{1, 2, 3, 4, 5, 6};
    auto ys = iter(xs)
                  .map<int>([](int x)
                            { return x + 1; })
                  .filter([](int x)
                          { return x > 4; })
                  .reverse()
                  .append({4, 3, 2, 1})
                  .drop(2)
                  .map<int>([](int x)
                            { return x * 2; })
                  .reverse()
                  .collect();

    for (auto i : ys)
        std::cout << i << " ";
    std::cout << std::endl;
    return 0;
}