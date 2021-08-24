#include <iostream>
#include <memory>
#include <cstring>
#include <optional>
#include <cmath>

enum class signum
{
    pos,
    neg
};

enum class cmp
{
    lt,
    eq,
    gt
};

struct pack
{
    std::unique_ptr<int[]> number;
    int length;
    signum sig;
    pack(std::unique_ptr<int[]> number_, int length_, signum sig_) : number(std::move(number_)),
                                                                     length(length_),
                                                                     sig(sig_) {}
};

std::optional<pack> parse_number(const char *number)
{
    if (strlen(number) < 1 || number == "-")
        return std::nullopt;

    const int len = strlen(number);
    int length = len;
    int j = 0;
    signum sig = signum::pos;

    if (number[0] == '-')
    {
        j++;
        length--;
        sig = signum::neg;
    }

    auto num = std::make_unique<int[]>(length);
    for (int i = j; i < len; i++)
    {
        if (number[i] < '0' || number[i] > '9')
            return std::nullopt;
        else
            num[i - j] = int(number[i] - '0');
    }

    return pack(std::move(num), length, sig);
}

class bn
{
private:
    std::unique_ptr<int[]> number;
    int length;
    signum sig;

    bn(std::unique_ptr<int[]> number_, int length_, signum sig_) : number(std::move(number_)),
                                                                   length(length_),
                                                                   sig(sig_) { shrink(); }

    void shrink()
    {
        int acc = 0;
        while (acc < length)
        {
            if (number[acc] == 0)
                acc++;
            else
                break;
        }
        if (acc == 0)
            return;
        else if (acc == length)
        {
            std::unique_ptr<int[]> tmp(new int[1]{0});
            number = std::move(tmp);
            length = 1;
            sig = signum::pos;
        }
        else
        {
            auto tmp = std::make_unique<int[]>(length - acc);
            for (int i = 0; i < length - acc; i++)
                tmp[i] = number[i + acc];
            number = std::move(tmp);
            length = length - acc;
        }
    }

public:
    bn(const char *number_)
    {
        auto result = parse_number(number_);
        if (result == std::nullopt)
        {
            std::unique_ptr<int[]> tmp(new int[1]{0});
            number = std::move(tmp);
            length = 1;
            sig = signum::pos;
        }
        else
        {
            number = std::move(result.value().number);
            length = result.value().length;
            sig = result.value().sig;
        }
    }

    bn(const bn &num)
    {
        auto tmp = num.clone();
        number = std::move(tmp.number);
        length = tmp.length;
        sig = tmp.sig;
    }

    ~bn() {}

    bn clone() const
    {
        auto tmp = std::make_unique<int[]>(length);
        for (int i = 0; i < length; i++)
            tmp[i] = number[i];
        return bn(std::move(tmp), length, sig);
    }

    bn negate() const
    {
        auto tmp = clone();
        if (tmp.sig == signum::neg)
            tmp.sig = signum::pos;
        else
            tmp.sig = signum::neg;
        return tmp;
    }

    bn &operator=(const bn &num)
    {
        auto tmp = num.clone();
        number = std::move(tmp.number);
        length = tmp.length;
        sig = tmp.sig;
        return *this;
    }

    friend std::ostream &operator<<(std::ostream &os, const bn &num)
    {
        if (num.sig == signum::neg)
            os << "-";
        for (int i = 0; i < num.length; i++)
            os << num.number[i];
        return os;
    }

    friend std::optional<cmp> compare_abseq(const bn &a, const bn &b)
    {
        if (a.length != b.length)
            return std::nullopt;
        for (int i = 0; i < a.length; i++)
        {
            if (a.number[i] > b.number[i])
                return cmp::gt;
            else if (a.number[i] < b.number[i])
                return cmp::lt;
            else
                continue;
        }
        return cmp::eq;
    }

    bool operator==(const bn &num) const
    {
        if (num.sig != sig || num.length != length)
            return false;
        return compare_abseq(*this, num).value() == cmp::eq;
    }

    bool operator>(const bn &num) const
    {
        if (sig == signum::pos && num.sig == signum::neg)
            return true;
        else if (sig == signum::neg && num.sig == signum::pos)
            return false;
        else if (sig == signum::pos && num.sig == signum::pos)
        {
            if (length > num.length)
                return true;
            else if (length < num.length)
                return false;
            else
                return compare_abseq(*this, num).value() == cmp::gt;
        }
        else
        {
            if (length > num.length)
                return false;
            else if (length < num.length)
                return true;
            else
                return compare_abseq(*this, num).value() == cmp::lt;
        }
    }

    bool operator>=(const bn &num) const
    {
        return (*this > num) || (*this == num);
    }

    bool operator<(const bn &num) const
    {
        return !(*this >= num);
    }

    bool operator<=(const bn &num) const
    {
        return !(*this > num);
    }

    bn operator+(const bn &x) const
    {
        if (sig == x.sig)
        {
            int len = std::max(length, x.length) + 1;
            auto tmp = std::make_unique<int[]>(len);
            int carry = 0;
            int p = len - length;
            int q = len - x.length;
            for (int i = len - 1; i >= 0; i--)
            {
                if (i - p >= 0 && i - q >= 0)
                {
                    int a = carry + number[i - p] + x.number[i - q];
                    tmp[i] = a % 10;
                    carry = a / 10;
                }
                else if (i - p >= 0)
                {
                    int a = carry + number[i - p];
                    tmp[i] = a % 10;
                    carry = a / 10;
                }
                else if (i - q >= 0)
                {
                    int a = carry + x.number[i - q];
                    tmp[i] = a % 10;
                    carry = a / 10;
                }
                else
                {
                    tmp[i] = carry;
                    carry = 0;
                }
            }

            return bn(std::move(tmp), len, sig);
        }
        else
        {
            if (sig == signum::pos && x.sig == signum::neg)
                return *this - x.negate();
            else
                return x - negate();
        }
    }

    bn operator-(const bn &x) const
    {
        if (sig != x.sig)
        {
            if (sig == signum::pos && x.sig == signum::neg)
                return *this + x.negate();
            else
                return (x + negate()).negate();
        }
        else
        {
            if (sig == signum::pos && x.sig == signum::pos)
            {
                if (*this > x)
                {
                    auto tmp =  std::make_unique<int[]>(length);
                    int borrowed = 0;
                    int p = length - x.length;
                    for (int i = length - 1; i >= 0; i--)
                        if (i - p >= 0)
                        {
                            if (number[i] < x.number[i - p] + borrowed)
                            {
                                tmp[i] = number[i] + 10 - x.number[i - p] - borrowed;
                                borrowed = 1;
                            }
                            else
                            {
                                tmp[i] = number[i] - x.number[i - p] - borrowed;
                                borrowed = 0;
                            }
                        }
                        else
                        {
                            tmp[i] = number[i] - borrowed;
                            borrowed = 0;
                        }
                    return bn(std::move(tmp), length, sig);
                }
                else
                {
                    return (x - *this).negate();
                }
            }
            else
            {
                return (negate() - x.negate()).negate();
            }
        }
    }

    bn operator*(const bn &x) const
    {
        signum s = signum::pos;
        if (sig != x.sig)
            s = signum::neg;
        const int len = length + x.length;
        int carry = 0;
        int p = len - 1;
        int q = p;

        std::unique_ptr<int[]> tmp(new int[len]);
        for (int i = 0; i < len; i++)
            tmp[i] = 0;

        for (int i = length - 1; i >= 0; i--)
        {
            p = q;
            for (int j = x.length - 1; j >= 0; j--)
            {
                int a = number[i] * x.number[j] + carry + tmp[p];
                tmp[p] = a % 10;
                carry = a / 10;
                p--;
            }
            while (p >= 0)
            {
                int a = carry + tmp[p];
                tmp[p] = a % 10;
                carry = a / 10;
                p--;
            }
            q--;
        }
        p = q;
        while (p >= 0)
        {
            int a = carry + tmp[p];
            tmp[p] = a % 10;
            carry = a / 10;
            p--;
        }

        return bn(std::move(tmp), len, s);
    }
};

int main()
{
    using namespace std;
    bn a = bn("23333333333333333333333");
    bn b = bn("-23333");
    bn c = bn("a");
    cout << a << endl;
    cout << b.clone() << endl;
    cout << c << endl;
    cout << int(a == b) << " " << int(a == a.clone()) << endl;
    cout << int(a > b) << " " << int(c <= b) << endl;
    cout << bn("933") << " + " << bn("200") << " = " << bn("933") + bn("200") << endl;
    cout << a << " - " << b << " = " << a - b << endl;
    cout << bn("256") - bn("64") << " " << bn("-25") - bn("75") << endl;
    cout << bn("199") - bn("287") << " " << bn("99900") + bn("100") << endl;
    cout << bn("23333333333333333") * bn("66666666666666") << endl;
    cout << bn("6") << " " << bn("-") << " " << bn("-3") << endl;
    return 0;
}
