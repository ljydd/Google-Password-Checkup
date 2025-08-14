import os, random, hashlib
from typing import List, Tuple


def egcd(a, b):
    if b == 0:
        return (1, 0, a)
    x, y, g = egcd(b, a % b)
    return (y, x - (a // b) * y, g)

def invmod(a, n):
    x, y, g = egcd(a, n)
    if g != 1:
        raise ValueError("no inverse")
    return x % n

def is_probable_prime(n, k=16):
    if n < 2:
        return False
    small_primes = [2,3,5,7,11,13,17,19,23,29]
    for p in small_primes:
        if n == p: return True
        if n % p == 0: return False
    # Miller-Rabin
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for _ in range(k):
        a = random.randrange(2, n - 2)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        skip = False
        for __ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                skip = True
                break
        if skip: 
            continue
        return False
    return True

def gen_prime(bits):
    while True:
        x = random.getrandbits(bits) | 1 | (1 << (bits - 1))
        if is_probable_prime(x):
            return x

# 安全群(DDH)：Z_p*的q子群

class DDHGroup:
    # 使用安全素数 p=2q+1，群G为阶q的子群，生成元g
    def __init__(self, q_bits=256):
        while True:
            q = gen_prime(q_bits)
            p = 2*q + 1
            if is_probable_prime(p):
                break
        # 选取g∈Z_p*，使得g^q ≡ 1 且 g^2 != 1
        while True:
            g = random.randrange(2, p-1)
            if pow(g, 2, p) != 1 and pow(g, q, p) == 1:
                break
        self.p = p
        self.q = q
        self.g = g

    def rand_exponent(self):
        return random.randrange(1, self.q)

    def hash_to_group(self, data: bytes):
        # H: U → G，映射为 g^{H'(x)}，简单实现
        h = int.from_bytes(hashlib.sha256(data).digest(), 'big') % self.q
        if h == 0: h = 1
        return pow(self.g, h, self.p)

# Paillier（加法同态）

class PaillierPublicKey:
    def __init__(self, n):
        self.n = n
        self.n2 = n*n
        self.g = n + 1  # 常见选择

    def encrypt(self, m: int):
        m = m % self.n
        while True:
            r = random.randrange(1, self.n)
            if egcd(r, self.n)[2] == 1:
                break
        # c = g^m * r^n mod n^2
        c = (pow(self.g, m, self.n2) * pow(r, self.n, self.n2)) % self.n2
        return c

    def e_mul_const(self, c, k):  # E(m)^k = E(k*m)
        return pow(c, k, self.n2)

    def e_mul(self, c1, c2):      # E(m1)*E(m2) = E(m1+m2)
        return (c1 * c2) % self.n2

    def rerand(self, c):
        # 重新随机化：乘以 E(0) = r^n
        while True:
            r = random.randrange(1, self.n)
            if egcd(r, self.n)[2] == 1:
                break
        return (c * pow(r, self.n, self.n2)) % self.n2

class PaillierSecretKey:
    def __init__(self, p, q, pub: PaillierPublicKey):
        self.p = p
        self.q = q
        self.n = p*q
        self.n2 = self.n*self.n
        self.pub = pub
        self.lam = (p-1)*(q-1)//egcd(p-1, q-1)[2]
        # μ = (L(g^λ mod n^2))^{-1} mod n
        u = pow(self.pub.g, self.lam, self.n2)
        L = (u - 1) // self.n
        self.mu = invmod(L, self.n)

    def decrypt(self, c: int):
        u = pow(c, self.lam, self.n2)
        L = (u - 1) // self.n
        m = (L * self.mu) % self.n
        return m

def paillier_keygen(bits=1024):
    # 生成 p,q 约等长
    p = gen_prime(bits//2)
    q = gen_prime(bits//2)
    n = p*q
    pub = PaillierPublicKey(n)
    sec = PaillierSecretKey(p, q, pub)
    return pub, sec

# 协议参与方

class Party1:
    # P1: 输入集合 V = {vi}
    def __init__(self, group: DDHGroup, V: List[bytes]):
        self.G = group
        self.V = V
        self.k1 = group.rand_exponent()  # 私钥指数
        self.Z_from_P2 = None            # 存 Round2 返回
        self.pk_from_P2 = None           # Paillier 公钥
        # 便于演示，记录cardinality
        self.last_cardinality = 0

    def round1(self):
        # 计算 {H(vi)^k1} 并打乱
        hashed_pow = [pow(self.G.hash_to_group(v), self.k1, self.G.p) for v in self.V]
        random.shuffle(hashed_pow)
        return hashed_pow

    def round3(self, P2_pairs: List[Tuple[int, int]]):
        # 输入：P2发来的 (H(wj)^k2, Enc(tj)) 的列表（已乱序）
        # 输出：返回 Enc(Σ_{match} tj) 的重新随机化密文
        assert self.Z_from_P2 is not None and self.pk_from_P2 is not None
        # 对每个对儿首元再乘k1次方，形成 H(wj)^{k1k2}
        lifted = [(pow(xk2, self.k1, self.G.p), ctt) for (xk2, ctt) in P2_pairs]
        # 找交集下标集合 J
        Zset = set(self.Z_from_P2)
        J_cts = [ctt for (tag, ctt) in lifted if tag in Zset]
        self.last_cardinality = len(J_cts)
        # 同态求和
        if not J_cts:
            # 空交集：返回 Enc(0)
            csum = self.pk_from_P2.encrypt(0)
        else:
            csum = J_cts[0]
            for c in J_cts[1:]:
                csum = self.pk_from_P2.e_mul(csum, c)
        # 重新随机化
        return self.pk_from_P2.rerand(csum)

class Party2:
    # P2: 输入对集 W = {(wi, ti)}，并生成Paillier密钥
    def __init__(self, group: DDHGroup, W: List[Tuple[bytes, int]], paillier_bits=1024):
        self.G = group
        self.W = W
        self.k2 = group.rand_exponent()
        self.pk, self.sk = paillier_keygen(paillier_bits)

    def round2(self, from_P1_list: List[int]):
        # 收到 {H(vi)^k1}，返回 Z={H(vi)^{k1k2}}（乱序）
        Z = [pow(x, self.k2, self.G.p) for x in from_P1_list]
        random.shuffle(Z)
        # 另外：对自身每个(wj,tj)，发送 (H(wj)^k2, Enc(tj))（乱序）
        pairs = []
        for (w, t) in self.W:
            hw = self.G.hash_to_group(w)
            tag = pow(hw, self.k2, self.G.p)
            ctt = self.pk.encrypt(t)
            pairs.append((tag, ctt))
        random.shuffle(pairs)
        return Z, pairs, self.pk

# 协议驱动

class DDH_PSI_Sum_Protocol:
    # 简单驱动，返回 (C, S)
    def __init__(self, V: List[bytes], W: List[Tuple[bytes, int]], q_bits=256, paillier_bits=1024):
        self.G = DDHGroup(q_bits=q_bits)
        self.P1 = Party1(self.G, V)
        self.P2 = Party2(self.G, W, paillier_bits=paillier_bits)

    def run(self):
        # Round 1 (P1 -> P2)
        msg1 = self.P1.round1()
        # Round 2 (P2 -> P1)
        Z, pairs, pk = self.P2.round2(msg1)
        # 缓存到P1
        self.P1.Z_from_P2 = Z
        self.P1.pk_from_P2 = pk
        # Round 3 (P1 -> P2)
        csum_rerand = self.P1.round3(pairs)
        # 输出
        S = self.P2.sk.decrypt(csum_rerand)  # 交集求和
        C = self.P1.last_cardinality         # 交集大小
        return C, S

# --------------------------- 演示 ---------------------------

def demo():
    # 构造测试数据（字符串->bytes）
    # 交集：id_20, id_30
    V = [f"id_{i}".encode() for i in [10,20,30,40,50,60,70]]
    W = []
    for i, t in [(5, 11),(15, 22),(20, 33),(25,44),(30,55),(35,66)]:
        W.append((f"id_{i}".encode(), t))
    proto = DDH_PSI_Sum_Protocol(V, W, q_bits=256, paillier_bits=1024)
    C, S = proto.run()
    print("交集大小 C =", C)  # 期望 2
    print("交集求和 S =", S)  # 期望 33 + 55 = 88

if __name__ == "__main__":
    random.seed(os.urandom(16))
    demo()
