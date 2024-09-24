import math
from primality import primality

def is_prime(n): 
    if n < 2: 
        return False 

    if n in (2, 3): 
        return True 

    if n % 2 == 0 or n % 3 == 0: 
        return False 

    i = 5 
    while i * i <= n: 
        if n % i == 0 or n % (i + 2) == 0: 
            return False 
        i += 6 

    return True 

 

# def is_prime(n) -> bool: 
#     if n < 2: 
#         return False 

#     for i in range(2, int(n**0.5) + 1): 
#         if n % i == 0: 
#             return False
#     return True 
 

# center should be odd
def find_prime(N = 2 ** 16, cnt = 10):
    diff = 2 * N
    now = (1 << 40) + 1 
    # now = 0x1fffffffffe00001
    while cnt > 0:
        if primality.isprime(now):
            print(hex(now))
            cnt -= 1
    
        now += diff

if __name__ == '__main__':
    find_prime()
