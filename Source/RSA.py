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


# Multiplicative inverse under modulo m for generating d
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


# Chinese remainder theorem
# xp = [ (y mod p)^(d mod (p-1)) ] mod p
# xq = [ (y mod q)^(d mod (q-1)) ] mod q
def chinese_remainder_theorem(a, d, p, q):
    d1 = d % (p - 1)
    d2 = d % (q - 1)

    xp = pow(a % p, d1, p)
    xq = pow(a % q, d2, q)

    m_inv = inv(p, q)
    w = xp + p * ((xq - xp) * m_inv % q)

    return w


# Prepare the 2 prime numbers P and Q for the Wiener attack
def generate_p_and_q_for_wiener():
    # q < p < 2q
    # 2 prime numbers p & q, each roughly the same size
    p = Crypto.Util.number.getPrime(1024)
    q = Crypto.Util.number.getPrime(1024)
    while p <= q or p >= 2 * q:
        p = Crypto.Util.number.getPrime(1024)
    return p, q


# ATTACK
def find_continuous_fractions(e, n):
    quotient = e // n  # floor approximation of the e/n fraction
    continuous_fraction = [quotient]
    while n * quotient != e:
        e, n = n, e % n
        quotient = e // n
        continuous_fraction.append(quotient)
    return continuous_fraction


# ATTACK
def check_criteria(l, d, n, e):
    find_d = {'found': False, 'private': {}}

    # l and d mustn't be 0
    if l == 0 or d == 0:
        return find_d

    # d must be odd, if d is even, we'll move on to the next convergent
    if d % 2 == 0:
        return find_d

    # PHI(N) must be a whole number
    # therefore (e*d - 1)/k must be a whole number.
    # (e*d - 1)/k is not a whole number, we'll move on to the next convergent!
    intermediary = e * d - 1
    if intermediary % l != 0:
        return find_d

    phi = intermediary // l

    a = 1
    b = (-1) * (n - phi + 1)
    c = n

    # PHI(N) is whole number => check if quadratic equation has integer solutions
    # x^2 - x * (n - phi(n) + 1) + n = 0
    delta = int(pow(b, 2) - 4 * a * c)
    if delta < 0:
        return find_d

    # find the 2 solutions of the quadratic equation
    # we verify if x1 * x2 = N => gives the factorization of N
    # and therefore we find the decryption exponent d
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


def attack_on_rsa(e, n):
    found = False
    private_key = {}

    # continuous fraction e/n approximates k/d
    # using continuous fractions, we can find a set of converging fractions to k/d and that approximate e/n
    frac = find_continuous_fractions(e, n)
    alpha = [frac[0], frac[0] * frac[1] + 1]  # alpha_0
    beta = [1, frac[1]]  # beta_0
    i = 0

    # exista l a.i. e * d - 1 = l * PHI(n)
    # [q1,q2,...,qk+1] = fractia continua asociata fractiei e/n => atunci exista un 1<=i<=k+1 a.i [q1,...,qi]=l/d
    # avand e si n, putem determina l si d astfel:

    while not found:  # while criteria(l,d)=1
        if i > 1:
            alpha.append(frac[i] * alpha[i - 1] + alpha[i - 2])  # alpha_i
            beta.append(frac[i] * beta[i - 1] + beta[i - 2])  # beta_i
        l = alpha[i]  # l = alpha_i
        d = beta[i]  # d = beta_i
        results = check_criteria(l, d, n, e)  # verif
        found = results['found']
        private_key = results['private']
        i += 1
    return private_key['d']


if __name__ == '__main__':

    print("[ (Secret keys) Generating P and Q numbers on 1024 bits ]")
    p = Crypto.Util.number.getPrime(1024)
    print("First prime number (P)", p)

    q = Crypto.Util.number.getPrime(1024)
    while p == q:
        q = Crypto.Util.number.getPrime(1024)
    print("Second prime number (Q): ", q)

    print("\n[ (Public key) Computing N = P * Q, on 2048 bits ]")
    N = p * q
    print("N = ", N)

    print("\n[ Computing Phi(N) = (p - 1)*(q - 1) ]")
    PHI = (p - 1) * (q - 1)
    print("PHI(N) =", PHI)

    print("\n[ (Public key) Generating the exponent number. (e < N) and (e mod Phi(N) != 0) and (e has max 32 bits) ]")
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

    print("\n[ Decrypting text using the FIRST METHOD ]")
    start = time.time()
    decrypted1 = encrypting(N, encrypted, d)
    print("Decrypted: ", decrypted1)
    print("Took %.3f seconds to decrypt the text!" % (time.time() - start))
    method1_time = (time.time() - start)

    print("[------------ VERIFICATION -------------]")
    print("[------------ dec(enc(x))=x -------------]")
    if decrypted1 == x:
        print("dec(enc(x))=x WORKED!")
    else:
        print("dec(enc(x))=x FAILED!")

    print("\n[ Decrypting text using the SECOND METHOD (TCR) ]")
    start = time.time()
    if p < q:
        decrypted2 = chinese_remainder_theorem(encrypted, d, p, q)
    else:
        decrypted2 = chinese_remainder_theorem(encrypted, d, q, p)
    print("Decrypted: ", decrypted2)
    print("Took %.3f seconds to decrypt the text!" % (time.time() - start))
    method2_time = (time.time() - start)

    if method1_time < method2_time:
        print("First decrypting method is quicker!")
    else:
        print("Second decrypting method is quicker!")

    # -----------
    print("\n[ WIENER ATTACK ]")
    print("Generating new values: ")

    # new P and Q
    new_p, new_q = generate_p_and_q_for_wiener()
    print("New P = ", new_p)
    print("New Q = ", new_q)

    # n = p * q  q<p<2q
    new_n = new_p * new_q
    print("New N = ", new_n)

    # phi(N) = (p - 1) * (q - 1)
    new_phi = (new_p - 1) * (new_q - 1)
    print("New Phi(N) = ", new_phi)

    # d < 1/3 * (N ^(1/4))
    print("\n[ (Small private key) Generating new d having maximum 510 bits ]")
    new_d = randrange(2, (math.isqrt(math.isqrt(new_n)) // 3))

    gcd_val = gcd(new_d, new_phi)
    while gcd_val != 1:
        new_d = randrange(2, (math.isqrt(math.isqrt(new_n)) // 3))
        gcd_val = gcd(new_d, new_phi)
    print("New d = ", new_d)

    # e = d^-1 mod Phi(N)
    new_e = inv(new_d, new_phi)
    print("New e = ", new_e)

    print("\n[ Starting the attack on RSA Alg (Small decryption exponent attack) ]")
    print("Attack will succeed if q < p <= 2q & d <= 1/3 * ( n^(1/4) )\n")
    start = time.time()
    hacked_d = attack_on_rsa(new_e, new_n)
    print("Hacked d value = ", hacked_d)

    # pratic, s au ales e si d a.i. e*d congruent cu 1 % phi, unde phi=(p-1)*(q-1) si d <(n^1/4)/3
    if new_d == hacked_d:
        print("WE FOUND D " + "in %.3f seconds!" % (time.time() - start))
    else:
        print("HACK FAILED " + "in %.3f seconds!" % (time.time() - start))
