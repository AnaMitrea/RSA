import math
import time
from random import randrange
import Crypto.Util.number


# Recursive GCD for RSA
def gcd(a, b):
    while a != 0:
        a, b = b % a, a
    return b


# Text encrypting for RSA
def encrypting(N, x, e):
    c = pow(x, e, N)
    return c


# Multiplicative inverse under modulo m for generating d number
def inv(a, m):
    m0 = m
    x0 = 0
    x1 = 1

    if m == 1:
        return 0

    # Apply extended Euclid Algorithm
    while a > 1:
        q = a // m  # q is quotient

        t = m

        # m is remainder now, process same as euclid's algo
        m = a % m
        a = t

        t = x0

        x0 = x1 - q * x0

        x1 = t

    # Make x1 positive
    if x1 < 0:
        x1 = x1 + m0

    return x1


# Prepare the 2 prime numbers P and Q for the Wiener attack

def generate_p_and_q_for_wiener():
    # p < q < 2p
    # 2 prime numbers p & q, each roughly the same size
    p = Crypto.Util.number.getPrime(1024)
    q = Crypto.Util.number.getPrime(1024)
    while p <= q or p >= 2 * q:
        p = Crypto.Util.number.getPrime(1024)
    return p, q


# == ATTACK ==
def rational_to_contfrac(x, y):
    quotient = x // y
    continuous_fraction = [quotient]
    while y * quotient != x:
        x, y = y, x % y
        quotient = x // y
        continuous_fraction.append(quotient)
    return continuous_fraction


# == ATTACK ==
def check_criterion(l, d, n, e):
    find_d = {'found': False, 'private': {}}

    if l == 0 or d == 0:
        return find_d

    if d % 2 == 0:
        return find_d

    intermediary = e * d - 1
    if intermediary % l != 0:
        return find_d

    phi = intermediary // l

    a = 1
    b = (-1) * (n - phi + 1)
    c = n

    # x^2 - x * (n - phi + 1) + n
    delta = int(pow(b, 2) - 4 * a * c)
    if delta < 0:
        return find_d

    square_root_of_delta = math.isqrt(delta)
    if square_root_of_delta * square_root_of_delta == delta:
        p = int(-b - square_root_of_delta)
        q = int(-b + square_root_of_delta)
        if p % 2 == 0 and q % 2 == 0 and p > 0 and q > 0:
            p = int(p // 2)
            q = int(q // 2)
            find_d['found'] = True
            find_d['private']['d'] = d

    return find_d


# == ATTACK ==
# Determinarea informațiilor private
def hack_RSA(e, n):
    # fie [q1,q2,...,qk+1] fractia continua asociata fractiei e/n
    # atunci exista un 1<=i<=k+1 a.i [q1,...,qi]=l/d
    # avand e si n, putem determina l si d in felul urmator
    found = False
    private_key = {}

    frac = rational_to_contfrac(e, n)
    alpha = [frac[0], frac[0] * frac[1] + 1]
    beta = [1, frac[1]]
    i = 0
    # repetam procedeul
    # i=i+1
    # determinam alpha_i si beta_i folosinf relatiile (1) si (2)
    # l=alpha_i; d=beta_i;
    # pana cand criteriu(l,d)=1

    # criteriu(l,d)={1, daca sistemul x*y=n si (x-1)*(y-1)=(e*d-1)/l are solutii intregi
    #              {0, altfel
    while not found:
        if i > 1:
            alpha.append(frac[i] * alpha[i - 1] + alpha[i - 2])
            beta.append(frac[i] * beta[i - 1] + beta[i - 2])
        l = alpha[i]
        d = beta[i]
        results = check_criterion(l, d, n, e)
        found = results['found']
        private_key = results['private']
        i += 1
    return private_key['d']


# Chinese remainder theorem
def mod2preExp(a, d, n, p, q):
    # xp=(y mod p)^(d mod (p-1)) mod p
    # xq=(y mod q)^(d mod (q-1)) mod q
    d1 = d % (p - 1)
    d2 = d % (q - 1)

    xp = pow(a % p, d1, p)
    xq = pow(a % q, d2, q)

    m1_inv = inv(p, q)
    w = xp + p * ((xq - xp) * m1_inv % q)

    return w


if __name__ == '__main__':

    print("[ Generating P and Q numbers on 1024 bits ]")
    p = Crypto.Util.number.getPrime(1024)
    print("First prime number (P)", p)

    q = Crypto.Util.number.getPrime(1024)
    while p == q:
        q = Crypto.Util.number.getPrime(1024)
    print("Second prime number (Q): ", q)

    print("\n[ Computing N = P * Q, on 2048 bits ]")
    N = p * q
    print("N = ", N)

    print("\n[ Computing Phi(N) = (p - 1)*(q - 1) ]")
    PHI = (p - 1) * (q - 1)
    print("PHI(N) =", PHI)

    print("\n[ Generating the exponent number. (e < N) and (e mod Phi(N) != 0) and (e has max 32 bits) ]")
    e = randrange(1, pow(2, 32))
    while gcd(e, PHI) != 1:
        e = randrange(1, pow(2, 32))
    print("e =", e)

    print("\n[ Generating d = e ^(-1) mod PHI(N) ]")
    d = inv(e, PHI)

    print("\n[ Choosing a random input x (1 < x < N) ] ")
    x = randrange(1, N)
    print("Plaintext: ", x)

    print("\n[ Starting encrypting input... ]")
    encrypted = encrypting(N, x, e)

    print("Encrypted text: ", encrypted)

    print("[------------ VERIFICATION -------------]")
    print("[------------ dec(enc(x))=x -------------]")
    print("\n[ Decrypting text using the FIRST METHOD ]")
    start = time.time()
    decrypted1 = encrypting(N, encrypted, d)
    print("Decrypted: ", decrypted1)
    print("Took %.3f seconds to decrypt the text!" % (time.time() - start))
    method1_time = (time.time() - start)

    print("\n[ Decrypting text using the SECOND METHOD ]")
    start = time.time()
    if p < q:
        decrypted2 = mod2preExp(encrypted, d, N, p, q)
    else:
        decrypted2 = mod2preExp(encrypted, d, N, q, p)

    print("Decriptare cu metoda 2: ", decrypted2)
    print("Aceasta decriptare dureaza %.3f secunde." % (time.time() - start))
    method2_time = (time.time() - start)

    if method1_time > method2_time:
        print("A doua decriptare a fost mai rapida decat prima!")
    else:
        print("Prima decriptare a fost mai rapida decat a doua!")
    # ==-------------------------------------------------------------------==
    print("\n == WIENER ATTACK ==")
    print("NEW VALUES:")

    # generam o pereche RSA vulnerabila
    new_p, new_q = generate_p_and_q_for_wiener()
    print("new_p = ", new_p)
    print("new_q = ", new_q)

    # n=p*q unde q<p<2q
    new_n = new_p * new_q
    print("new_n = ", new_n)

    # phi=(p-1)*(q-1)
    new_phi = (new_p - 1) * (new_q - 1)
    print("new_phi = ", new_phi)

    # d<1/3 *N ^(1/4)
    new_d = randrange(2, (math.isqrt(math.isqrt(new_n)) // 3))
    val = gcd(new_d, new_phi)
    while val != 1:
        new_d = randrange(2, (math.isqrt(math.isqrt(new_n)) // 3))
        val = gcd(new_d, new_phi)
    print("new_d = ", new_d)

    # e=d^-1 mod phi
    new_e = Crypto.Util.number.inverse(new_d, new_phi)
    print("new_e = ", new_e)

    start = time.time()
    # inceperea atacului
    hacked_d = hack_RSA(new_e, new_n)
    print("hacked_d = ", hacked_d)

    # pratic, s au ales e si d a.i. e*d congruent cu 1 % phi, unde phi=(p-1)*(q-1) si d <(n^1/4)/3
    if new_d == hacked_d:
        print("Hack WORKED!")
    else:
        print("Hack FAILED")
    print("in  %.3f secunde." % (time.time() - start))
    print("----------FINAL---------------")
