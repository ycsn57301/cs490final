import math

class Complex:
    def __init__(self, re, im):
        self.re = re
        self.im = im

    def mul(self, that):
        real = self.re * that.re - self.im * that.im
        imag = self.re * that.im + self.im * that.re
        return Complex(real, imag)
    
    def add(self, that):
        return Complex(self.re + that.re, self.im + that.im)

    def sub(self, that):
        return Complex(self.re - that.re, self.im - that.im)
    
    def pow(self, exponent):
        result = Complex(1, 0)
        value = Complex(self.re, self.im)
        while (exponent > 0):
            if exponent % 2 == 1:
                result = result.mul(value)
            value = value.mul(value)
            exponent = exponent >> 1
        return result
    
def bitreverse(n, bits):
    count = bits - 1
    reverse = n
    n = n >> 1
    while n > 0:
        reverse = (reverse << 1) | (n & 1)
        n = n >> 1
        count = count - 1
    return ((reverse << count) & ((1 << bits) - 1))

def radix2fft(fields, omega):
    n = len(fields)
    logn = math.floor( math.log(n) / math.log(2) )

    if n == 1:
        return
    
    for k in range(0, n):
        rk = bitreverse(k, logn)
        if k < rk:
            t = fields[k]
            fields[k] = fields[rk]
            fields[rk] = t
    
    m = 1
    for s in range(1, logn + 1):
        w_m = omega.pow(math.floor(n / (2*m)))
        for k in range(0, n, 2*m):
            w = Complex(1, 0)
            for j in range(0, m):
                t = w.mul(fields[k+j+m])
                fields[k+j+m] = fields[k+j].sub(t)
                fields[k+j] = fields[k+j].add(t)
                w = w.mul(w_m)
        m = m * 2

fields = [Complex(0, 1), Complex(0, 2), Complex(0, 3), Complex(0, 4), Complex(1, 1), Complex(1, 2), Complex(1, 3), Complex(1, 4)]
radix2fft(fields, Complex(0, 1))
for c in fields:
    print(c.re, c.im)