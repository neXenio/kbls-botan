/*
* (C) 2014,2015,2016,2018 Jack Lloyd
* (C) 2016 Daniel Neus, Rohde & Schwarz Cybersecurity
*
* Botan is released under the Simplified BSD License (see license.txt)
*/

#include "tests.h"
#include <iostream>
#include <botan/cipher_mode.h>
#include <botan/block_cipher.h>

#if defined(BOTAN_HAS_KYBER)
#include <botan/kyber.h>
#include <botan/rng.h>
#include <botan/auto_rng.h>
#include <botan/hex.h>
#endif

namespace Botan_Tests {

    namespace {

#if defined(BOTAN_HAS_KYBER)

        // Kyber test RNG
#define RNG_SUCCESS      0
#define RNG_BAD_MAXLEN  -1
#define RNG_BAD_OUTBUF  -2
#define RNG_BAD_REQ_LEN -3
        #include <string.h>


        typedef struct {
            unsigned char   buffer[16];
            int             buffer_pos;
            unsigned long   length_remaining;
            unsigned char   key[32];
            unsigned char   ctr[16];
        } AES_XOF_struct;

        typedef struct {
            unsigned char   Key[32];
            unsigned char   V[16];
            int             reseed_counter;
        } AES256_CTR_DRBG_struct;


        AES256_CTR_DRBG_struct  DRBG_ctx;

        void    AES256_ECB( unsigned char* key, unsigned char* ctr, unsigned char* buffer );

        /*
         seedexpander_init()
         ctx            - stores the current state of an instance of the seed expander
         seed           - a 32 byte random value
         diversifier    - an 8 byte diversifier
         maxlen         - maximum number of bytes (less than 2**32) generated under this seed and diversifier
         */
        int
            seedexpander_init( AES_XOF_struct* ctx,
                unsigned char* seed,
                unsigned char* diversifier,
                unsigned long maxlen )
        {
            if ( maxlen >= 0x100000000 )
                return RNG_BAD_MAXLEN;

            ctx->length_remaining = maxlen;

            memcpy( ctx->key, seed, 32 );

            memcpy( ctx->ctr, diversifier, 8 );
            ctx->ctr[11] = maxlen % 256;
            maxlen >>= 8;
            ctx->ctr[10] = maxlen % 256;
            maxlen >>= 8;
            ctx->ctr[9] = maxlen % 256;
            maxlen >>= 8;
            ctx->ctr[8] = maxlen % 256;
            memset( ctx->ctr + 12, 0x00, 4 );

            ctx->buffer_pos = 16;
            memset( ctx->buffer, 0x00, 16 );

            return RNG_SUCCESS;
        }

        /*
         seedexpander()
            ctx  - stores the current state of an instance of the seed expander
            x    - returns the XOF data
            xlen - number of bytes to return
         */
        int
            seedexpander( AES_XOF_struct* ctx, unsigned char* x, unsigned long xlen )
        {
            unsigned long   offset;

            if ( x == NULL )
                return RNG_BAD_OUTBUF;
            if ( xlen >= ctx->length_remaining )
                return RNG_BAD_REQ_LEN;

            ctx->length_remaining -= xlen;

            offset = 0;
            while ( xlen > 0 ) {
                if ( xlen <= ( 16 - ctx->buffer_pos ) ) { // buffer has what we need
                    memcpy( x + offset, ctx->buffer + ctx->buffer_pos, xlen );
                    ctx->buffer_pos += xlen;

                    return RNG_SUCCESS;
                }

                // take what's in the buffer
                memcpy( x + offset, ctx->buffer + ctx->buffer_pos, 16 - ctx->buffer_pos );
                xlen -= 16 - ctx->buffer_pos;
                offset += 16 - ctx->buffer_pos;

                AES256_ECB( ctx->key, ctx->ctr, ctx->buffer );
                ctx->buffer_pos = 0;

                //increment the counter
                for ( int i = 15; i >= 12; i-- ) {
                    if ( ctx->ctr[i] == 0xff )
                        ctx->ctr[i] = 0x00;
                    else {
                        ctx->ctr[i]++;
                        break;
                    }
                }

            }

            return RNG_SUCCESS;
        }

        void
            AES256_CTR_DRBG_Update( unsigned char* provided_data,
                unsigned char* Key,
                unsigned char* V )
        {
            unsigned char   temp[48];

            for ( int i = 0; i < 3; i++ ) {
                //increment V
                for ( int j = 15; j >= 0; j-- ) {
                    if ( V[j] == 0xff )
                        V[j] = 0x00;
                    else {
                        V[j]++;
                        break;
                    }
                }

                AES256_ECB( Key, V, temp + 16 * i );
            }
            if ( provided_data != NULL )
                for ( int i = 0; i < 48; i++ )
                    temp[i] ^= provided_data[i];
            memcpy( Key, temp, 32 );
            memcpy( V, temp + 32, 16 );
        }

        // Use whatever AES implementation you have. This uses AES from openSSL library
        //    key - 256-bit AES key
        //    ctr - a 128-bit plaintext value
        //    buffer - a 128-bit ciphertext value
        void
            AES256_ECB( unsigned char* key, unsigned char* ctr, unsigned char* buffer )
        {
            std::unique_ptr<Botan::BlockCipher> cipher( Botan::BlockCipher::create( "AES-256" ) );

            std::vector<uint8_t> keyAes( key, key + cipher->maximum_keylength() );
            std::vector<uint8_t> block( ctr, ctr + cipher->block_size() );


            cipher->set_key( keyAes );
            cipher->encrypt( block );

            std::copy( block.begin(), block.end(), buffer );
        }

        void
            randombytes_init( const unsigned char* entropy_input,
                unsigned char* personalization_string,
                int security_strength )
        {
            unsigned char   seed_material[48];

            memcpy( seed_material, entropy_input, 48 );
            if ( personalization_string )
                for ( int i = 0; i < 48; i++ )
                    seed_material[i] ^= personalization_string[i];
            memset( DRBG_ctx.Key, 0x00, 32 );
            memset( DRBG_ctx.V, 0x00, 16 );
            AES256_CTR_DRBG_Update( seed_material, DRBG_ctx.Key, DRBG_ctx.V );
            DRBG_ctx.reseed_counter = 1;
        }

        int
            randombytes( unsigned char* x, unsigned long long xlen )
        {
            unsigned char   block[16];
            int             i = 0;

            while ( xlen > 0 ) {
                //increment V
                for ( int j = 15; j >= 0; j-- ) {
                    if ( DRBG_ctx.V[j] == 0xff )
                        DRBG_ctx.V[j] = 0x00;
                    else {
                        DRBG_ctx.V[j]++;
                        break;
                    }
                }
                AES256_ECB( DRBG_ctx.Key, DRBG_ctx.V, block );
                if ( xlen > 15 ) {
                    memcpy( x + i, block, 16 );
                    i += 16;
                    xlen -= 16;
                }
                else {
                    memcpy( x + i, block, xlen );
                    xlen = 0;
                }
            }
            AES256_CTR_DRBG_Update( NULL, DRBG_ctx.Key, DRBG_ctx.V );
            DRBG_ctx.reseed_counter++;

            return RNG_SUCCESS;
        }

        class Kyber_Test_RNG final : public Botan::RandomNumberGenerator
        {
        public:
            std::string name() const override { return "Kyber_Test_RNG"; }

            void clear() override
            {
                // reset struct
                // TO DO
            }

            bool accepts_input() const override { return true; }

            void add_entropy( const uint8_t data[], size_t len ) override
            {
                randombytes_init( data, nullptr, 256 );
            }

            bool is_seeded() const override
            {
                return true;
            }

            void randomize( uint8_t out[], size_t len ) override
            {
                // TO DO
                randombytes( out, len );
            }

            Kyber_Test_RNG( const std::vector<uint8_t>& seed )
            {
                add_entropy( seed.data(), seed.size() );
            }
        };

        class KYBER_Tests final : public Test
        {
        public:
            Test::Result run_kyber_test( Botan::KyberMode mode )
            {
                std::string test_name;
                switch ( mode )
                {
                case Botan::KyberMode::Kyber512:
                    test_name = "kyber512 test API";
                    break;
                case Botan::KyberMode::Kyber768:
                    test_name = "kyber768 test API";
                    break;
                case Botan::KyberMode::Kyber1024:
                    test_name = "kyber1024 test API";
                    break;
                default:
                    throw std::runtime_error( "unknown kyber mode in run_kyber_test()" );;
                }

                Test::Result result( test_name );

                uint8_t salt[1];
                size_t shared_secret_length = 32;

                // Alice
                std::unique_ptr<Botan::RandomNumberGenerator> kyber_rng_alice;
                kyber_rng_alice.reset( new Botan::AutoSeeded_RNG );
                auto priv_key = Botan::Kyber_PrivateKey( *kyber_rng_alice, mode );

                // Bob
                std::unique_ptr<Botan::RandomNumberGenerator> kyber_rng_bob;
                kyber_rng_bob.reset( new Botan::AutoSeeded_RNG );
                auto pub_key = Botan::Kyber_PublicKey( priv_key.public_key_bits(), mode );
                auto enc = pub_key.create_kem_encryption_op( *kyber_rng_bob, "", "" );
                Botan::secure_vector<uint8_t> cipher_text, key_bob;
                enc->kem_encrypt( cipher_text, key_bob, shared_secret_length, *kyber_rng_bob, salt, 0 );

                // Alice
                auto dec = priv_key.create_kem_decryption_op( *kyber_rng_alice, "", "" );
                auto key_alice = dec->kem_decrypt( cipher_text.data(), cipher_text.size(), shared_secret_length, salt, 0 );

                result.test_eq( "Shared secrets are not equal!", key_alice == key_bob, true );
                return result;

            }
            std::vector<Test::Result> run() override
            {
                std::vector<Test::Result> results;

                results.push_back( run_kyber_test( Botan::KyberMode::Kyber512 ) );
                results.push_back( run_kyber_test( Botan::KyberMode::Kyber768 ) );
                results.push_back( run_kyber_test( Botan::KyberMode::Kyber1024 ) );

                return results;
            }
        };

        BOTAN_REGISTER_TEST( "kyber", KYBER_Tests );



        class KYBER_KAT_Tests final : public Text_Based_Test
        {
        public:
            KYBER_KAT_Tests() : Text_Based_Test( "pubkey/kyber_512.vec", "count,seed,pk,sk,ct,ss" ) {}


            Test::Result run_one_test( const std::string&, const VarMap& vars ) override
            {
                const auto round = vars.get_req_sz( "count" );
                Test::Result result( "KYBER_KAT Round " + std::to_string( round ) );

                // read input from test file
                std::vector<uint8_t> seed_in = vars.get_req_bin( "seed" );
                std::vector<uint8_t> pk_in = vars.get_req_bin( "pk" );
                std::vector<uint8_t> sk_in = vars.get_req_bin( "sk" );
                std::vector<uint8_t> ct_in = vars.get_req_bin( "ct" );
                std::vector<uint8_t> ss_in = vars.get_req_bin( "ss" );

                uint8_t salt[1];
                size_t shared_secret_length = 32;

                // Kyber test RNG
                std::unique_ptr<Botan::RandomNumberGenerator> kyber_test_rng;
                kyber_test_rng.reset( new Kyber_Test_RNG( seed_in ) );

                // Alice            
                auto priv_key = Botan::Kyber_PrivateKey( *kyber_test_rng, Botan::KyberMode::Kyber512 );
                result.test_eq( "Public Key Output", priv_key.public_key_bits(), pk_in );
                result.test_eq( "Secret Key Output", priv_key.private_key_bits(), sk_in );

                // Bob
                auto pub_key = Botan::Kyber_PublicKey( priv_key.public_key_bits(), Botan::KyberMode::Kyber512 );
                auto enc = pub_key.create_kem_encryption_op( *kyber_test_rng, "", "" );
                Botan::secure_vector<uint8_t> cipher_text, key_bob;
                enc->kem_encrypt( cipher_text, key_bob, shared_secret_length, *kyber_test_rng, salt, 0 );
                result.test_eq( "Cipher-Text Output", cipher_text, ct_in );
                result.test_eq( "Key B Output", key_bob, ss_in );

                // Alice
                auto dec = priv_key.create_kem_decryption_op( *kyber_test_rng, "", "" );
                auto key_alice = dec->kem_decrypt( cipher_text.data(), cipher_text.size(), shared_secret_length, salt, 0 );
                result.test_eq( "Key A Output", key_alice, ss_in );

                return result;
            }
        };

        BOTAN_REGISTER_TEST( "kyber_kat", KYBER_KAT_Tests );
#endif 

    };

}