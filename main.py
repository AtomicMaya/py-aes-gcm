from typing import List, Tuple
from functools import reduce
from values import sbox

################################################## UTILITIES ##################################################

def repr(m: List[int]):
  """ Prints an array out as a string of its contents in hexadecimal """
  return ' '.join(list(map(lambda x: hex(x)[2:].zfill(2), m))).upper() # Eg. 12 = '0xc' -> 'c' -> '0c' -> '0C'

def repr2(m: List[List[int]]):
  """ Prints a 2D array out as a string of its contents in hexadecimal, row by row """
  return '\n'.join([' '.join(list(map(lambda x: hex(x)[2:].zfill(2), _m))).upper() for _m in m])

def convert_from_ascii(message: str) -> List[int]:
  """ Converts a string into a list of its characters' ASCII values """
  return list(map(lambda x: ord(x), message))

def convert_to_ascii(block: List[int]) -> str:
  """ Converts a list of ASCII values into the string they represent """
  return ''.join(list(map(lambda x: chr(x), block)))
  
def split_to_blocks(message: List[int]) -> List[List[int]]:
  """ Divides a list of numbers into blocks of 16 integers. """
  return [message[i*16:(i+1)*16] for i in range(len(message) // 16)]

def get_sbox_value(values: List[int]) -> List[int]:
  """ Substitute values provided with the value at that position in the AES SBox """
  return [sbox[i] for i in values]

def xor(*values: List[List[int]]) -> List[int]:
  """ Performs a linear XOR among a number of lists of same size. """
  assert min(list(map(len, values))) == max(list(map(len, values))), 'Cannot XOR Lists, different list sizes.'
  return [reduce(lambda x, y: x ^ y, map(lambda z: z[i], values)) for i in range(min(list(map(len, values))))]

################################################## CONSTANTS ##################################################

rc = [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]

def rcon(i: int) -> List[int]:
  """ Generates a constant to be used in the key expansion process """
  return [rc[i], 0x00, 0x00, 0x00]

def n(key: List[int]) -> int:
  """ Returns the number of 32-bit words in the key """
  return [4, 6, 8][len(key) * 2 // 16 - 2]

def rounds(key: List[int]) -> int:
  """ Returns the amount of rounds the AES algorithm will do in order to encrypt or decrypt a message """
  return [10, 12, 14][len(key) * 2 // 16 - 2]

def split_key(k: List[int]) -> List[List[int]]:
  """ Breaks up a key into 32-bit words """
  return [k[i*4:(i+1)*4] for i in range(len(k) // 4)]

################################################## SUBKEY GENERATION ##################################################

def generate_subkeys(key: List[int]) -> List[List[int]]:
  """ Generate the subkeys necessary for AES encryption and decryption """
  N = n(key)
  K = split_key(key)
  R = rounds(key) + 1
  W = []

  for i in range(R*4):
    if i < N:
      W += [K[i]]
    elif i >= N and i % N == 0:
      W += [xor(W[i - N], get_sbox_value(rotate(W[i - 1])), rcon(i // N))]
    elif i >= N and N > 6 and i % N == 4:
      W += [xor(W[i - N], get_sbox_value(W[i - 1]))]
    else:
      W += [xor(W[i - N], W[i - 1])]

  return [[el for arr in W[i*4:i*4+4] for el in arr] for i in range(R)] # Generates the subkeys by grouping words in groups of 4.
  
def rotate(row: List[int], right=True) -> List[int]:
  """ Performs a rotation on a list in the direction specified by :param right """
  return row[1:] + [row[0]] if right else [row[3]] + row[0:3]

def block_to_matrix(block: List[int]) -> List[List[int]]:
  """ Transforms a 128-bit word into a matrix equivalent """
  return [[block[i*4+j] for i in range(16 // 4)] for j in range(16 // 4)]

def matrix_to_block(matrix: List[List[int]]) -> List[int]:
  """ Transforms a matrix into its 128-bit word equivalent """
  return [matrix[i][j] for j in range(4) for i in range(4)]

################################################## MIX COLUMN UTILITIES ##################################################

def mix_column(fixed_matrix: List[List[int]], matrix: List[List[int]]) -> List[List[int]]:
  """ Performs the Mix Column operation on a matrix (profided with a fixed matrix that is used as a GF reference). """
  assert min(list(map(len, fixed_matrix))) == max(list(map(len, fixed_matrix))) and min(list(map(len, matrix))) == max(list(map(len, matrix))), 'Cannot mix these matrices. Matrix definition unbalanced.'
  assert min(list(map(len, fixed_matrix))) == max(list(map(len, matrix))), 'Matrix definition unequal.'

  size = min(list(map(len, fixed_matrix)))
  # Performs an XOR on each value resulting from the GF multiplication of each respective number in the fixed_matrix and the given matrix.
  # The given matrix is transposed first to improve legibility.
  return [[reduce(lambda x, y: x ^ y, [gf_multiplication_7(a, b) for a, b in zip(fixed_matrix[i], transpose_square_matrix(matrix=matrix)[j])]) for j in range(size)] for i in range(size)]

def transpose_square_matrix(matrix: List[List[int]]) -> List[List[int]]:
  """ Transposes a square matrix to more easily access data elements """
  assert min(list(map(len, matrix))) == max(list(map(len, matrix))), 'Cannot transpose this matrix. Matrix definition unbalanced.'
  assert max(list(map(len, matrix))) == len(matrix), 'Cannot transpose this matrix. Matrix is not square.'
  return [[matrix[j][i] for j in range(len(matrix))] for i in range(len(matrix))]

def shift_row(matrix: List[List[int]], right=True):
  """ Performs a linear shift of the rows of a matrix. The direction of the shift can be toggled. """
  for i in range(len(matrix)):
    for _ in range(1, i+1): # Each row of a matrix (indexed by i=0..4) needs to be rotated i times.
      matrix[i] = rotate(matrix[i], right=right)
  return matrix

############################## NEW FUNCS

def gf_multiplication(pn1: int, pn2: int, polynomial: int, limit: int) -> int:
  """ Russian Peasant Multiplication algorithm, used to factor polynomials efficiently in GF(2^n) """
  p = 0
  while pn1 > 0 and pn2 > 0:
    if pn2 & 1 != 0:
      p ^= pn1
    if pn1 & limit != 0: # 0x80 = 0b1000 0000 = 128. If the bit at 2^7 is set, then the number is greater than 128 and needs to be shifted.
      pn1 = (pn1 << 1) ^ polynomial
    else:
      pn1 <<= 1
    
    pn2 >>= 1
  return p

def gf_multiplication_7(pn1: int, pn2: int) -> int:
  """ GF(2^7), with polynomial X^8 + X^7 + X^2 + X + 1"""
  return gf_multiplication(pn1, pn2, polynomial=0x11b, limit=0x80)

def gf_multiplication_128(pn1: int, pn2: int) -> int:
  """ GF(2^128), with polynomial X^128 + X^7 + X^2 + X + 1"""
  return gf_multiplication(pn1, pn2, polynomial=0x100000000000000000000000000000087, limit=(1 << 127))  

def block_to_number(block: List[int]) -> int:
  """ Converts a 128-bit block to the number it represents. """
  res: int = 0
  for z in list(zip(range(len(block)-1, -1, -1),block))[::-1]:
    res ^= z[1] << ((z[0])*8) # Every block item is stored on 8 bits.
  return res

def number_to_block(number: int) -> List[int]:
  """ Converts a number to the 128-bit block represented by it. """
  res: List[int] = []
  for i in range(16):
    res += [(number & (0xFF << i * 8)) >> i * 8]
  return res[::-1]

################################################## AES ENCRYPTION & DECRYPTION #################################################

def aes_encrypt(msg: List[int], key: List[int]):
  """ Encrypts a given message with a given key. """
  assert len(key) * 8 in [128, 192, 256], "Key size must be 128, 192 or 256 bits (16, 24 or 32 characters)"
  
  # Static Galois Field multiplication matrix.
  gf_matrix = block_to_matrix([0x02, 0x01, 0x01, 0x03, 0x03, 0x02, 0x01, 0x01, 0x01, 0x03, 0x02, 0x01, 0x01, 0x01, 0x03, 0x02])
  subkeys = generate_subkeys(key=key)
  
  blocks = split_to_blocks(message=msg)     # And split the message in 16-sized blocks

  for i in range(len(blocks)):             # ECB allows one to operate on each block individually.
    blocks[i] = xor(blocks[i], subkeys[0]) # Round 0 operation, XOR-ing with the 4 first 32-bit words of the key.

    for s in range(1, len(subkeys)):
      # Substitute the values in the SBoxes, transform the result to a matrix and perform the Shift Row operation.
      blocks[i] = shift_row(block_to_matrix(get_sbox_value(blocks[i])), right=True)
      if s != len(subkeys) - 1:                            # If it is not the last round.
        blocks[i] = mix_column(gf_matrix, blocks[i])       # Perform the Mix Column Operation
      blocks[i] = xor(matrix_to_block(blocks[i]), subkeys[s])   # Transform this matrix to a block again and perform an xor with the relevant round key.

  return [item for block in blocks for item in block]           # Flatten the resulting array.

def compute_ghash(x: List[List[int]], h: int) -> List[int]:
  """ 
  @param x a list of numbers, all of bitsize 128.
  @param h the hash subkey
  @return ym a 128-bit number
  """
  assert len(list(filter(lambda j: not j, map(lambda i: len(i) * 8 == 128, x)))) == 0, "GHASH: components of bit string x have irregular size (len(x) != 128m)"
  
  y0 = [0 for _ in range(16)] # y0 is 0^128 ie. an array of 16 bytes all 0.
  y = [y0]
  for i in range(len(x)): # while we can consume a block in x -> x_i
    y += [number_to_block(gf_multiplication_128(block_to_number(xor(y[i], x[i])), h))]
  return y[-1]

def compute_hash_subkey(key: List[int]) -> int:
  """ Generates the hash subkey, which is an AES encryption of an empty bitstring with the key."""
  assert len(key) * 8 in [128, 192, 256], 'Key size must be 128, 192 or 256 bits (16, 24 or 32 characters)'
  return block_to_number(aes_encrypt([0 for _ in range(16)], key))

def compute_initial_counter_block(iv: List[int], h: int) -> List[int]:
  """ Generates the counter block from the IV, with bifurcated behavior depending on whether the IV is 12 bytes long. """
  j0: List[int] = []
  if (len(iv) * 8 == 96):
    j0 = [*iv, 0x00, 0x00, 0x00, 0x01]
  else:
    number_of_blocks = ((len(iv) * 8) // 128) + 1
    iv_blocks: List[List[int]] = [iv[16*i:16*(i+1)] for i in range(number_of_blocks)]
    iv_blocks[-1] = [*iv_blocks[-1], *[0 for _ in range(16 - len(iv_blocks[-1]))]]
    iv_blocks += [[0 for _ in range(8)] + number_to_block(len(iv)*8)[-8:]]
    j0 = compute_ghash(iv_blocks, h)

  return j0

def inc_32(block: List[int]) -> List[int]:
  """ Increments the 32 least bits by 1 mod 2**32 """
  return block[:12] + number_to_block((block_to_number(block[12:]) + 1) % (2**32))[-4:]

def compute_gctr(cb: List[int], key: List[int], x: List[int]) -> List[int]:
  """ 
  Applies the Galois counter process to the provided list of bits.
  
  :param cb The counter block
  :param key The key
  :param x The block to pass through the Galois counter
  """
  number_of_blocks = ((len(x) * 8) // 128) + 1
  x_blocks: List[List[int]] = [x[16*i:16*(i+1)] for i in range(number_of_blocks)]
  counter_values: List[List[int]] = [cb]
  y_blocks: List[List[int]] = []
  for i in range(number_of_blocks):
    counter_values += [inc_32(counter_values[-1])]
    y_blocks += [xor(aes_encrypt(counter_values[i], key)[:len(x_blocks[i])], x_blocks[i])]

  return [el for arr in y_blocks for el in arr]

def _gcm_encrypt(p: List[int], key: List[int], iv: List[int], a: List[int]) -> Tuple[List[int], List[int]]:
  """ 
  Encrypts the plaintext p using the Galois counter mode, providing a ciphertext and a tag.
  
  :param p The plaintext
  :param key The key
  :param iv The initialisation vector
  :param a The additional authentication data
  :return (c, t) The ciphertext and the tag
  """
  h = compute_hash_subkey(key)
  icb: List[int] = compute_initial_counter_block(iv, h) #j0
  ciphertext: List[int] = compute_gctr(inc_32(icb), key, p)
  v: int = 128 * ((len(a) * 8) // 128 + 1) - (len(a) * 8)
  u: int = 128 * ((len(ciphertext) * 8) // 128 + 1) - (len(ciphertext) * 8)
  pre_s: List[int] = a + [0 for _ in range(v//8)] + ciphertext + [0 for _ in range(u//8)] + number_to_block(len(a) * 8)[-8:] + number_to_block(len(ciphertext) * 8)[-8:]
  
  s: List[int] = compute_ghash([pre_s[16*i:16*(i+1)] for i in range((len(pre_s) * 8) // 128)], h)
  t: List[int] = compute_gctr(icb, key, s)
  return (ciphertext, t)

def _gcm_decrypt(c: List[int], key: List[int], iv: List[int], a: List[int], t: List[int]) -> List[int]:
  """ 
  Decrypts the ciphertext c using the Galois counter mode, providing a plaintext.
  
  :param c The ciphertext
  :param key The key
  :param iv The initialisation vector
  :param a The additional authentication data
  :param t The tag
  :return (p) The plaintext
  """
  h = compute_hash_subkey(key)
  icb: List[int] = compute_initial_counter_block(iv, h) #j0
  
  v: int = 128 * ((len(a) * 8) // 128 + 1) - (len(a) * 8)
  u: int = 128 * ((len(c) * 8) // 128 + 1) - (len(c) * 8)
  pre_s: List[int] = a + [0 for _ in range(v//8)] + c + [0 for _ in range(u//8)] + number_to_block(len(a) * 8)[-8:] + number_to_block(len(c) * 8)[-8:]
  s: List[int] = compute_ghash([pre_s[16*i:16*(i+1)] for i in range((len(pre_s) * 8) // 128)], h)
  computed_t: List[int] = compute_gctr(icb, key, s)
  if computed_t != t:
    return convert_from_ascii("FAIL")
  else:
    plaintext: List[int] = compute_gctr(inc_32(icb), key, c)
    return plaintext


def gcm_encrypt(msg: str, key: str, iv: str, a: str) -> Tuple[List[int], List[int]]:
  """ Helper function that takes encryption parameters as base strings and calls the correct function with the converted content. """
  return _gcm_encrypt(convert_from_ascii(msg), convert_from_ascii(key), convert_from_ascii(iv), convert_from_ascii(a))

def gcm_decrypt(ciphertext: str, key: str, iv: str, a: str, tag: str) -> List[int]:
  """ Helper function that takes decryption parameters as base strings and calls the correct function with the converted content. """
  return _gcm_decrypt(convert_from_ascii(ciphertext), convert_from_ascii(key), convert_from_ascii(iv), convert_from_ascii(a), convert_from_ascii(tag))

################################################## TEST & EXECUTION ##################################################

def test_gcm(msg: str, key: str, iv: str, a: str):
  """ Does a *le test* on the *le code* to see if it *le works* """
  print('Plaintext')
  print(repr2([convert_from_ascii(msg)[16*i:16*(i+1)] for i in range((len(convert_from_ascii(msg)) * 8) // 128 + 1)]), end='\n\n')
  print('Key')
  print(repr(convert_from_ascii(key)), end='\n\n')
  
  print('IV')
  print(repr(convert_from_ascii(iv)), end='\n\n')
  print('A')
  print(repr(convert_from_ascii(a)), end='\n\n')

  ciphertext, tag = gcm_encrypt(msg, key, iv, a)
  print('Ciphertext')
  print(repr2([ciphertext[16*i:16*(i+1)] for i in range((len(ciphertext) * 8) // 128 + 1)]), end='\n\n')

  print('Tag')
  print(repr(tag), end='\n\n')

  plaintext = gcm_decrypt(convert_to_ascii(ciphertext), key, iv, a, convert_to_ascii(tag))
  
  if convert_to_ascii(plaintext) == "FAIL":
    print("FAILURE: TAGS DON'T MATCH")
    return

  print('Computed Plaintext')
  print(repr2([plaintext[16*i:16*(i+1)] for i in range((len(plaintext) * 8) // 128 + 1)]), end='\n\n')

  assert msg == convert_to_ascii(plaintext), "AES-GCM decryption has failed"
  print("Success!")
  print(f'The plaintext was:\n"{convert_to_ascii(plaintext)}"')

if __name__ == '__main__':
  test_gcm("Bob and Alice went for a walk in the fuckity fucken park at fuckall in the morn cos they hadn't much else to", "You can't see me", "Some bitching IV string my ass", "useless")