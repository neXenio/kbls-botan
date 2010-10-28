/*
* Rivest's Package Tranform
*
* (C) 2009 Jack Lloyd
*
* Distributed under the terms of the Botan license
*/

#include <botan/package.h>
#include <botan/filters.h>
#include <botan/ctr.h>
#include <botan/get_byte.h>
#include <botan/internal/xor_buf.h>

namespace Botan {

void aont_package(RandomNumberGenerator& rng,
                  BlockCipher* cipher,
                  const byte input[], size_t input_len,
                  byte output[])
   {
   const size_t BLOCK_SIZE = cipher->block_size();

   if(!cipher->valid_keylength(BLOCK_SIZE))
      throw Invalid_Argument("AONT::package: Invalid cipher");

   // The all-zero string which is used both as the CTR IV and as K0
   const std::string all_zeros(BLOCK_SIZE*2, '0');

   SymmetricKey package_key(rng, BLOCK_SIZE);

   Pipe pipe(new StreamCipher_Filter(new CTR_BE(cipher), package_key));

   pipe.process_msg(input, input_len);
   pipe.read(output, pipe.remaining());

   // Set K0 (the all zero key)
   cipher->set_key(SymmetricKey(all_zeros));

   SecureVector<byte> buf(BLOCK_SIZE);

   const size_t blocks =
      (input_len + BLOCK_SIZE - 1) / BLOCK_SIZE;

   byte* final_block = output + input_len;
   clear_mem(final_block, BLOCK_SIZE);

   // XOR the hash blocks into the final block
   for(u32bit i = 0; i != blocks; ++i)
      {
      const size_t left = std::min<size_t>(BLOCK_SIZE,
                                           input_len - BLOCK_SIZE * i);

      zeroise(buf);
      copy_mem(&buf[0], output + BLOCK_SIZE * i, left);

      for(size_t j = 0; j != sizeof(i); ++j)
         buf[BLOCK_SIZE - 1 - j] ^= get_byte(sizeof(i)-1-j, i);

      cipher->encrypt(buf);

      xor_buf(final_block, buf, BLOCK_SIZE);
      }

   // XOR the random package key into the final block
   xor_buf(final_block, package_key.begin(), BLOCK_SIZE);
   }

void aont_unpackage(BlockCipher* cipher,
                    const byte input[], size_t input_len,
                    byte output[])
   {
   const size_t BLOCK_SIZE = cipher->block_size();

   if(!cipher->valid_keylength(BLOCK_SIZE))
      throw Invalid_Argument("AONT::unpackage: Invalid cipher");

   if(input_len < BLOCK_SIZE)
      throw Invalid_Argument("AONT::unpackage: Input too short");

   // The all-zero string which is used both as the CTR IV and as K0
   const std::string all_zeros(BLOCK_SIZE*2, '0');

   cipher->set_key(SymmetricKey(all_zeros));

   SecureVector<byte> package_key(BLOCK_SIZE);
   SecureVector<byte> buf(BLOCK_SIZE);

   // Copy the package key (masked with the block hashes)
   copy_mem(&package_key[0],
            input + (input_len - BLOCK_SIZE),
            BLOCK_SIZE);

   const size_t blocks = ((input_len - 1) / BLOCK_SIZE);

   // XOR the blocks into the package key bits
   for(u32bit i = 0; i != blocks; ++i)
      {
      const size_t left = std::min<size_t>(BLOCK_SIZE,
                                           input_len - BLOCK_SIZE * (i+1));

      zeroise(buf);
      copy_mem(&buf[0], input + BLOCK_SIZE * i, left);

      for(size_t j = 0; j != sizeof(i); ++j)
         buf[BLOCK_SIZE - 1 - j] ^= get_byte(sizeof(i)-1-j, i);

      cipher->encrypt(buf);

      xor_buf(&package_key[0], buf, BLOCK_SIZE);
      }

   Pipe pipe(new StreamCipher_Filter(new CTR_BE(cipher), package_key));

   pipe.process_msg(input, input_len - BLOCK_SIZE);

   pipe.read(output, pipe.remaining());
   }

}
