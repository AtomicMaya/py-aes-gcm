from typing import List
from functools import reduce
from values import sbox, sbox_inverse
from pprint import pprint

################################################## UTILITIES ##################################################

def repr(m: List[int]):
  """ Prints an array out as a string of its contents in hexadecimal """
  return ' '.join(list(map(lambda x: hex(x)[2:].zfill(2), m))).upper() # Eg. 12 = '0xc' -> 'c' -> '0c' -> '0C'

def repr2(m: List[List[int]]):
  return '\n'.join([' '.join(list(map(lambda x: hex(x)[2:].zfill(2), _m))).upper() for _m in m])

def convert_from_ascii(message: str) -> List[int]:
  """ Converts a string into a list of its characters' ASCII values """
  return list(map(lambda x: ord(x), message))

def convert_to_ascii(block: List[int]) -> str:
  """ Converts a list of ASCII values into the string they represent """
  return ''.join(list(map(lambda x: chr(x), block)))

def pad(block: List[int]) -> List[int]:
  """ AES padding function, in order to always arrive at blocks of a length that is a multiple of 16 """
  missing = 16 - (len(block) % 16) # Eg. for len = 9 -> missing = 7, for len = 39 -> missing = 9
  return block + (missing * [missing]) # Append to the block a block containing 'missing' times the number of missing values.

def unpad(block: List[int]) -> List[int]:
  """ Removes the padding added by the pad function """
  return block[:-block[-1]] # In pad the value appended is the number of added values, so we can use it as a basis to slice our block again.

def split_to_blocks(message: List[int]) -> List[List[int]]:
  """ Divides a list of numbers into blocks of 16 integers. """
  return [message[i*16:(i+1)*16] for i in range(len(message) // 16)]

def get_sbox_value(values: List[int]) -> List[int]:
  """ Substitute values provided with the value at that position in the AES SBox """
  return [sbox[i] for i in values]

""" Reverse the ssbstitution of values provided with the value at that position in the AES Inverse SBox """
def get_inverse_sbox_value(values: List[int]) -> List[int]:
  return [sbox_inverse[i] for i in values]

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

def gf_multiplication_7(pn1: int, pn2: int) -> int:
  """ Russian Peasant Multiplication algorithm, used to factor polynomials efficiently in GF(2^n) """
  p = 0
  while pn1 > 0 and pn2 > 0:
    if pn2 & 1 != 0:
      p ^= pn1
    if pn1 & 0x80 != 0: # 0x80 = 0b1000 0000 = 128. If the bit at 2^7 is set, then the number is greater than 128 and needs to be shifted.
      pn1 = (pn1 << 1) ^ 0x11b
    else:
      pn1 <<= 1
    
    pn2 >>= 1
  return p

# Converts a 128-bit block to the number it represents.
def convert_block_to_number(block: List[int]) -> int:
  res: int = 0
  for z in list(zip(range(len(block)-1, -1, -1),block))[::-1]:
    res ^= z[1] << ((z[0])*8) # Every block item is stored on 8 bits.
  return res

def convert_number_to_block(number: int) -> List[int]:
  res: List[int] = []
  for i in  range(16):
    res += [(number & (0xFF << i * 8)) >> i * 8]
  return res[::-1]

def gf_multiplication_128(pn1: int, pn2: int) -> int:
  """ Russian Peasant Multiplication algorithm, used to factor polynomials efficiently in GF(2^n) """
  p = 0
  while pn1 > 0 and pn2 > 0:
    if pn2 & 1 != 0:
      p ^= pn1
    if pn1 & (1 << 127) != 0: # 0x80 = 0b1000 0000 = 128. If the bit at 2^7 is set, then the number is greater than 128 and needs to be shifted.
      pn1 = (pn1 << 1) ^ 0x100000000000000000000000000000087
    else:
      pn1 <<= 1
    pn2 >>= 1
  return p
  

################################################## AES ENCRYPTION & DECRYPTION #################################################

def aes_encrypt(msg: List[int], key: List[int]):
  """ Encrypts a given message with a given key. """
  assert len(key) * 8 in [128, 192, 256], 'Key size must be 128, 192 or 256 bits (16, 24 or 32 characters)'
  
  # Static Galois Field multiplication matrix.
  gf_matrix = block_to_matrix([0x02, 0x01, 0x01, 0x03, 0x03, 0x02, 0x01, 0x01, 0x01, 0x03, 0x02, 0x01, 0x01, 0x01, 0x03, 0x02])
  subkeys = generate_subkeys(key=key)
  
  msg = pad(msg)                            # Pad the original message to a length multiple of 16
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

def aes_decrypt(msg: List[int], key: List[int]):
  """ Decrypts a given message with a given key. """
  assert len(key) * 8 in [128, 192, 256], 'Key size must be 128, 192 or 256 bits (16, 24 or 32 characters)'

  gf_matrix = block_to_matrix([0x0e, 0x09, 0x0d, 0x0b, 0x0b, 0x0e, 0x09, 0x0d, 0x0d, 0x0b, 0x0e, 0x09, 0x09, 0x0d, 0x0b, 0x0e])
  subkeys = generate_subkeys(key=key)

  blocks = split_to_blocks(message=msg) # Split the message in 16-sized blocks

  for i in range(len(blocks)):                  # ECB allows one to operate on each block individually.
    for s in range(len(subkeys) - 1, 0, -1):    # Work rounds backwards.
      blocks[i] = block_to_matrix(xor(blocks[i], subkeys[s]))                           # Perform an xor with the relevant round key, and then convert it to a matrix
      if s != len(subkeys) - 1:
        blocks[i] = mix_column(gf_matrix, blocks[i])                                    # Perform the Mix Column Operation
      blocks[i] = get_inverse_sbox_value(matrix_to_block(shift_row(blocks[i], right=False)))  # Perform the reverse Shift Row operation, transform the result to a block and substitute with values from the inverse SBoxes
    blocks[i] = xor(blocks[i], subkeys[0])                                              # Reverse the round 0 operation
  
  return unpad([item for block in blocks for item in block]) # Flatten the decrypted blocks and unpad the result.

def compute_hash_subkey(key: str) -> List[int]:
  return aes_encrypt([0 for _ in range(16)], convert_from_ascii(key))

def gcm_encrypt(msg: str, key: str, iv: str, a: str) -> Tuple[List[int], List[int]]:
  hash_subkey: List[int] = compute_hash_subkey(key)



  pass

################################################## TEST & EXECUTION ##################################################

def test(msg: str, key: str):
  """ Checks whether or not the provided AES algorithm works at encoding and decoding a specific string for a specific key. """
  _msg = convert_from_ascii(msg)
  _key = convert_from_ascii(key)
  
  print('Original Plaintext:\t', msg)
  print('Key:\t\t\t', key, '\n')
  print('Original:\t\t', repr(_msg), '\n')
  msg_encrypted = aes_encrypt(msg=_msg, key=_key)
  print('Encrypted:\t\t', repr(msg_encrypted), '\n')
  msg_decrypted = aes_decrypt(msg=msg_encrypted, key=_key)
  print('Decrypted:\t\t', repr(msg_decrypted))
  print('Decrypted Plaintext:\t', convert_to_ascii(msg_decrypted))

  assert msg_decrypted == _msg, 'AES does not work'
  print('\n', '#' * 150, '\n', sep='')

if __name__ == '__main__':
  #test('Two One Nine Two', 'Thats my Kung Fu')
  #test('Can you smell what the Rock is cooking?', 'You can\'t see me')

  gcm_encrypt("", "", "", "")