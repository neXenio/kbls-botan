#include <botan/kyber.h>
#include <botan/rng.h>

#include <botan/hash.h>
#include <botan/mem_ops.h>
#include <botan/pubkey.h>
#include <botan/sha3.h>
#include <botan/shake.h>

namespace
{
    using namespace Botan;
    class Kyber_Internal_Operation final
    {
    public:


        typedef struct {
            // TODO Use m_N
            int16_t coeffs[256]; // coeffs[m_N]
        } poly;

        typedef struct {
            // TODO Use m_k
            poly vec[4]; // vec[m_k]
        } polyvec;


        /*************************************************
        * Name:        csubq
        *
        * Description: Conditionallly subtract q
        *
        * Arguments:   - int16_t x: input integer
        *
        * Returns:     a - q if a >= q, else a
        **************************************************/
        int16_t csubq(int16_t a) {
            a -= m_Q;
            a += (a >> 15) & m_Q;
            return a;
        }

        /*************************************************
        * Name:        poly_csubq
        *
        * Description: Applies conditional subtraction of q to each coefficient
        *              of a polynomial. For details of conditional subtraction
        *              of q see comments in reduce.c
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void poly_csubq(poly *r)
        {
            unsigned int i;
            for (i = 0;i<m_N;i++)
                r->coeffs[i] = csubq(r->coeffs[i]);
        }

        /*************************************************
        * Name:        poly_tobytes
        *
        * Description: Serialization of a polynomial
        *
        * Arguments:   - uint8_t *r: pointer to output byte array
        *                            (needs space for KYBER_POLYBYTES bytes)
        *              - poly *a:    pointer to input polynomial
        *              TO DO XXX
        **************************************************/
        void poly_tobytes( std::vector<uint8_t>& r, size_t offset_r, poly* a )
        {
            unsigned int i;
            uint16_t t0, t1;

            poly_csubq( a );

            for ( i = 0; i < get_n() / 2; i++ ) {
                t0 = a->coeffs[2 * i];
                t1 = a->coeffs[2 * i + 1];
                r[3 * i + 0 + offset_r] = ( t0 >> 0 );
                r[3 * i + 1 + offset_r] = ( t0 >> 8 ) | ( t1 << 4 );
                r[3 * i + 2 + offset_r] = ( t1 >> 4 );
            }
        }


        /*************************************************
        * Name:        poly_tobytes
        *
        * Description: Serialization of a polynomial
        *
        * Arguments:   - uint8_t *r: pointer to output byte array
        *                            (needs space for KYBER_POLYBYTES bytes)
        *              - poly *a:    pointer to input polynomial
        *              TO DO XXX
        **************************************************/
        void poly_tobytes( secure_vector<uint8_t>& r, size_t offset_r, poly* a )
        {
            unsigned int i;
            uint16_t t0, t1;

            poly_csubq( a );

            for ( i = 0; i < get_n() / 2; i++ ) {
                t0 = a->coeffs[2 * i];
                t1 = a->coeffs[2 * i + 1];
                r[3 * i + 0 + offset_r] = ( t0 >> 0 );
                r[3 * i + 1 + offset_r] = ( t0 >> 8 ) | ( t1 << 4 );
                r[3 * i + 2 + offset_r] = ( t1 >> 4 );
            }
        }


        /*************************************************
        * Name:        poly_compress
        *
        * Description: Compression and subsequent serialization of a polynomial
        *
        * Arguments:   - uint8_t *r: pointer to output byte array
        *                            (of length KYBER_POLYCOMPRESSEDBYTES)
        *              - poly *a:    pointer to input polynomial
        **************************************************/
        void poly_compress( secure_vector<uint8_t>& r, poly* a )
        {
            unsigned int i, j;
            uint8_t t[8];

            poly_csubq( a );

            if( m_k == 2 || m_k == 3 )
            {
                size_t offset = 0;
                for ( i = 0; i < m_N / 8; i++ ) {
                    for ( j = 0; j < 8; j++ )
                        t[j] = ( ( ( (uint16_t)a->coeffs[8 * i + j] << 4 ) + m_Q / 2 ) / m_Q) & 15;

                    r[0 + m_poly_vec_compressed_bytes + offset] = t[0] | ( t[1] << 4 );
                    r[1 + m_poly_vec_compressed_bytes + offset] = t[2] | ( t[3] << 4 );
                    r[2 + m_poly_vec_compressed_bytes + offset] = t[4] | ( t[5] << 4 );
                    r[3 + m_poly_vec_compressed_bytes + offset] = t[6] | ( t[7] << 4 );
                    offset += 4;
                }
            }
            else if( m_k == 4 )
            {
                size_t offset = 0;
                for ( i = 0; i < m_N / 8; i++ ) {
                    for ( j = 0; j < 8; j++ )
                        t[j] = ( ( ( (uint32_t)a->coeffs[8 * i + j] << 5 ) + m_Q / 2 ) / m_Q) & 31;

                    r[0 + m_poly_vec_compressed_bytes + offset] = ( t[0] >> 0 ) | ( t[1] << 5 );
                    r[1 + m_poly_vec_compressed_bytes + offset] = ( t[1] >> 3 ) | ( t[2] << 2 ) | ( t[3] << 7 );
                    r[2 + m_poly_vec_compressed_bytes + offset] = ( t[3] >> 1 ) | ( t[4] << 4 );
                    r[3 + m_poly_vec_compressed_bytes + offset] = ( t[4] >> 4 ) | ( t[5] << 1 ) | ( t[6] << 6 );
                    r[4 + m_poly_vec_compressed_bytes + offset] = ( t[6] >> 2 ) | ( t[7] << 3 );
                    offset += 5;
                }
            }
            else
            {
                throw std::runtime_error( "KYBER_POLYCOMPRESSEDBYTES needs to be in {128, 160}" );
            }
        }


        /*************************************************
        * Name:        polyvec_tobytes
        *
        * Description: Serialize vector of polynomials
        *
        * Arguments:   - std::vector<uint8_t> *r: pointer to output byte array
        *                            (needs space for KYBER_POLYVECBYTES)
        *              - polyvec *a: pointer to input vector of polynomials
        *              TO DO XXX
        **************************************************/
        void polyvec_tobytes( std::vector<uint8_t>& r, polyvec* a )
        {
            for ( unsigned int i = 0; i < get_k(); i++ )
                poly_tobytes( r, i * get_poly_bytes(), &a->vec[i] );
        }


        /*************************************************
        * Name:        polyvec_tobytes
        *
        * Description: Serialize vector of polynomials
        *
        * Arguments:   - std::vector<uint8_t> *r: pointer to output byte array
        *                            (needs space for KYBER_POLYVECBYTES)
        *              - polyvec *a: pointer to input vector of polynomials
        *              TO DO XXX
        **************************************************/
        void polyvec_tobytes( secure_vector<uint8_t>& r, polyvec* a )
        {
            for ( unsigned int i = 0; i < get_k(); i++ )
                poly_tobytes( r, i * get_poly_bytes(), &a->vec[i] );
        }


        /*************************************************
        * Name:        polyvec_csubq
        *
        * Description: Applies conditional subtraction of q to each coefficient
        *              of each element of a vector of polynomials
        *              for details of conditional subtraction of q see comments in
        *              reduce.c
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void polyvec_csubq(polyvec *r)
        {
            unsigned int i;
            for (i = 0;i<m_k;i++)
                poly_csubq(&r->vec[i]);
        }


        /*************************************************
        * Name:        polyvec_compress
        *
        * Description: Compress and serialize vector of polynomials
        *
        * Arguments:   - uint8_t *r: pointer to output byte array
        *                            (needs space for KYBER_POLYVECCOMPRESSEDBYTES)
        *              - polyvec *a: pointer to input vector of polynomials
        **************************************************/
        void polyvec_compress( secure_vector<uint8_t>& r, polyvec* a )
        {
            unsigned int i, j, k;

            polyvec_csubq( a );

            if ( m_k == 4 )
            {
                uint16_t t[8];
                size_t offset = 0;
                for ( i = 0; i < m_k; i++ ) {
                    for ( j = 0; j < m_N / 8; j++ ) {
                        for ( k = 0; k < 8; k++ )
                            t[k] = ( ( ( (uint32_t)a->vec[i].coeffs[8 * j + k] << 11 ) + m_Q / 2 )
                                / m_Q ) & 0x7ff;

                        r[0 + offset] = ( t[0] >> 0 );
                        r[1 + offset] = ( t[0] >> 8 ) | ( t[1] << 3 );
                        r[2 + offset] = ( t[1] >> 5 ) | ( t[2] << 6 );
                        r[3 + offset] = ( t[2] >> 2 );
                        r[4 + offset] = ( t[2] >> 10 ) | ( t[3] << 1 );
                        r[5 + offset] = ( t[3] >> 7 ) | ( t[4] << 4 );
                        r[6 + offset] = ( t[4] >> 4 ) | ( t[5] << 7 );
                        r[7 + offset] = ( t[5] >> 1 );
                        r[8 + offset] = ( t[5] >> 9 ) | ( t[6] << 2 );
                        r[9 + offset] = ( t[6] >> 6 ) | ( t[7] << 5 );
                        r[10 + offset] = ( t[7] >> 3 );
                        offset += 11;
                    }
                }
            }
            else if ( m_k == 2 || m_k == 3 )
            {
                uint16_t t[4];
                size_t offset = 0;
                for ( i = 0; i < m_k; i++ ) {
                    for ( j = 0; j < m_N / 4; j++ ) {
                        for ( k = 0; k < 4; k++ )
                            t[k] = ( ( ( (uint32_t)a->vec[i].coeffs[4 * j + k] << 10 ) + m_Q / 2 )
                                / m_Q ) & 0x3ff;

                        r[0 + offset] = ( t[0] >> 0 );
                        r[1 + offset] = ( t[0] >> 8 ) | ( t[1] << 2 );
                        r[2 + offset] = ( t[1] >> 6 ) | ( t[2] << 4 );
                        r[3 + offset] = ( t[2] >> 4 ) | ( t[3] << 6 );
                        r[4 + offset] = ( t[3] >> 2 );
                        offset += 5;
                    }
                }
            }
            else
            {
                throw std::runtime_error( "KYBER_POLYCOMPRESSEDBYTES needs to be in {320*KYBER_K, 352*KYBER_K}" );
            }
        }


        /*************************************************
        * Name:        polyvec_decompress
        *
        * Description: De-serialize and decompress vector of polynomials;
        *              approximate inverse of polyvec_compress
        *
        * Arguments:   - polyvec *r:       pointer to output vector of polynomials
        *              - const uint8_t *a: pointer to input byte array
        *                                  (of length KYBER_POLYVECCOMPRESSEDBYTES)
        **************************************************/
        void polyvec_decompress( polyvec* r,
            const uint8_t* a, size_t a_len )
        {
            unsigned int i, j, k;

            if( a_len == m_k * 352 + m_poly_compressed_bytes )
            {
                uint16_t t[8];
                for ( i = 0; i < m_k; i++ ) {
                    for ( j = 0; j < m_N / 8; j++ ) {
                        t[0] = ( a[0] >> 0 ) | ( (uint16_t)a[1] << 8 );
                        t[1] = ( a[1] >> 3 ) | ( (uint16_t)a[2] << 5 );
                        t[2] = ( a[2] >> 6 ) | ( (uint16_t)a[3] << 2 ) | ( (uint16_t)a[4] << 10 );
                        t[3] = ( a[4] >> 1 ) | ( (uint16_t)a[5] << 7 );
                        t[4] = ( a[5] >> 4 ) | ( (uint16_t)a[6] << 4 );
                        t[5] = ( a[6] >> 7 ) | ( (uint16_t)a[7] << 1 ) | ( (uint16_t)a[8] << 9 );
                        t[6] = ( a[8] >> 2 ) | ( (uint16_t)a[9] << 6 );
                        t[7] = ( a[9] >> 5 ) | ( (uint16_t)a[10] << 3 );
                        a += 11;

                        for ( k = 0; k < 8; k++ )
                            r->vec[i].coeffs[8 * j + k] = ( (uint32_t)( t[k] & 0x7FF ) * m_Q + 1024 ) >> 11;
                    }
                }
            }
            else if( a_len == m_k * 320 + m_poly_compressed_bytes )
            {
                uint16_t t[4];
                for ( i = 0; i < m_k; i++ ) {
                    for ( j = 0; j < m_N / 4; j++ ) {
                        t[0] = ( a[0] >> 0 ) | ( (uint16_t)a[1] << 8 );
                        t[1] = ( a[1] >> 2 ) | ( (uint16_t)a[2] << 6 );
                        t[2] = ( a[2] >> 4 ) | ( (uint16_t)a[3] << 4 );
                        t[3] = ( a[3] >> 6 ) | ( (uint16_t)a[4] << 2 );
                        a += 5;

                        for ( k = 0; k < 4; k++ )
                            r->vec[i].coeffs[4 * j + k] = ( (uint32_t)( t[k] & 0x3FF ) * m_Q + 512 ) >> 10;
                    }
                }
            }
            else
            {
                throw std::runtime_error( "KYBER_POLYVECCOMPRESSEDBYTES needs to be in {320*KYBER_K, 352*KYBER_K}" );
            }
        }


        /*************************************************
        * Name:        poly_frombytes
        *
        * Description: De-serialization of a polynomial;
        *              inverse of poly_tobytes
        *
        * Arguments:   - poly *r:          pointer to output polynomial
        *              - const uint8_t *a: pointer to input byte array
        *                                  (of KYBER_POLYBYTES bytes)
        *                                  TO DO XXX
        **************************************************/
        void poly_frombytes( poly* r, const std::vector<uint8_t> a, size_t offset )
        {
            for ( size_t i = 0; i < get_n() / 2; i++ )
            {
                r->coeffs[2 * i] = ( ( a[3 * i + 0 + offset] >> 0 ) | ( (uint16_t)a[3 * i + 1 + offset] << 8 ) ) & 0xFFF;
                r->coeffs[2 * i + 1] = ( ( a[3 * i + 1 + offset] >> 4 ) | ( (uint16_t)a[3 * i + 2 + offset] << 4 ) ) & 0xFFF;
            }
        }



        /*************************************************
        * Name:        polyvec_frombytes
        *
        * Description: De-serialize vector of polynomials;
        *              inverse of polyvec_tobytes
        *
        * Arguments:   - uint8_t *r:       pointer to output byte array
        *              - const polyvec *a: pointer to input vector of polynomials
        *                                  (of length KYBER_POLYVECBYTES)
        *                                  TO DO XXX
        **************************************************/
        void polyvec_frombytes( polyvec* r, const std::vector<uint8_t> a )
        {
            for ( size_t i = 0; i < get_k(); i++ )
                poly_frombytes( &r->vec[i], a, i * get_poly_bytes() );
        }


        /*************************************************
        * Name:        pack_ciphertext
        *
        * Description: Serialize the ciphertext as concatenation of the
        *              compressed and serialized vector of polynomials b
        *              and the compressed and serialized polynomial v
        *
        * Arguments:   uint8_t *r: pointer to the output serialized ciphertext
        *              poly *pk:   pointer to the input vector of polynomials b
        *              poly *v:    pointer to the input polynomial v
        **************************************************/
        void pack_ciphertext( secure_vector<uint8_t>& r,
            polyvec* b,
            poly* v )
        {
            polyvec_compress( r, b );
            poly_compress( r, v );
        }


        /*************************************************
        * Name:        unpack_sk
        *
        * Description: De-serialize the secret key;
        *              inverse of pack_sk
        *
        * Arguments:   - polyvec *sk:             pointer to output vector of
        *                                         polynomials (secret key)
        *              - const uint8_t *packedsk: pointer to input serialized secret key
        **************************************************/
        void unpack_sk( polyvec* sk,
            const std::vector<uint8_t> packedsk )
        {
            polyvec_frombytes( sk, packedsk );
        }


        /*************************************************
        * Name:        unpack_pk
        *
        * Description: De-serialize public key from a byte array;
        *              approximate inverse of pack_pk
        *
        * Arguments:   - polyvec *pk:             pointer to output public-key
        *                                         polynomial vector
        *              - uint8_t *seed:           pointer to output seed to generate
        *                                         matrix A
        *              - const uint8_t *packedpk: pointer to input serialized public key
        *              TO DO XXX
        **************************************************/
        void unpack_pk( polyvec* pk,
            secure_vector<uint8_t>& seed,
            const std::vector<uint8_t>& packedpk )
        {
            polyvec_frombytes( pk, packedpk );
            for ( size_t i = 0; i < get_sym_bytes(); i++ )
                seed[i] = packedpk[i + get_poly_vec_bytes()];
        }


        /*************************************************
        * Name:        poly_add
        *
        * Description: Add two polynomials
        *
        * Arguments: - poly *r:       pointer to output polynomial
        *            - const poly *a: pointer to first input polynomial
        *            - const poly *b: pointer to second input polynomial
        **************************************************/
        void poly_add(poly *r, const poly *a, const poly *b)
        {
            unsigned int i;
            for (i = 0;i<m_N;i++)
                r->coeffs[i] = a->coeffs[i] + b->coeffs[i];
        }

        /*************************************************
        * Name:        polyvec_add
        *
        * Description: Add vectors of polynomials
        *
        * Arguments: - polyvec *r:       pointer to output vector of polynomials
        *            - const polyvec *a: pointer to first input vector of polynomials
        *            - const polyvec *b: pointer to second input vector of polynomials
        **************************************************/
        void polyvec_add(polyvec *r, const polyvec *a, const polyvec *b)
        {
            unsigned int i;
            for (i = 0;i<m_k;i++)
                poly_add(&r->vec[i], &a->vec[i], &b->vec[i]);
        }


        /*************************************************
        * Name:        poly_tomont
        *
        * Description: Inplace conversion of all coefficients of a polynomial
        *              from normal domain to Montgomery domain
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void poly_tomont(poly *r)
        {
            unsigned int i;
            const int16_t f = (1ULL << 32) % m_Q;
            for (i = 0;i<m_N;i++)
                r->coeffs[i] = montgomery_reduce((int32_t)r->coeffs[i] * f);
        }


        /*************************************************
        * Name:        polyvec_reduce
        *
        * Description: Applies Barrett reduction to each coefficient
        *              of each element of a vector of polynomials
        *              for details of the Barrett reduction see comments in reduce.c
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void polyvec_reduce(polyvec *r)
        {
            unsigned int i;
            for (i = 0;i<m_k;i++)
                poly_reduce(&r->vec[i]);
        }


        /*************************************************
        * Name:        polyvec_invntt_tomont
        *
        * Description: Apply inverse NTT to all elements of a vector of polynomials
        *              and multiply by Montgomery factor 2^16
        *
        * Arguments:   - polyvec *r: pointer to in/output vector of polynomials
        **************************************************/
        void polyvec_invntt_tomont(polyvec *r)
        {
            unsigned int i;
            for (i = 0;i<m_k;i++)
                poly_invntt_tomont(&r->vec[i]);
        }


        /*************************************************
        * Name:        prf
        *
        * Description: Usage of SHAKE256 as a PRF, concatenates secret and public input
        *              and then generates outlen bytes of SHAKE256 output
        *
        * Arguments:   - const uint8_t *key: pointer to the key
        *                                    (of length KYBER_SYMBYTES)
        *              - uint8_t nonce:      single-byte nonce (public PRF input)
        * Return:       Output
        **************************************************/
        secure_vector<uint8_t> prf(
            const uint8_t key[32],
            uint8_t nonce)
        {
            if (!m_kyber_90s)
            {
                // TODO only normal kyber no 90s
                unsigned int i;
                uint8_t extkey[m_sym_bytes + 1];

                for (i = 0;i<m_sym_bytes;i++)
                    extkey[i] = key[i];
                extkey[i] = nonce;

                secure_vector< uint64_t > spongeState;
                spongeState.resize(25);
                size_t spongeStatePos = 0;

                spongeStatePos = Botan::SHA_3::absorb(m_SHAKE256_RATE, spongeState, spongeStatePos, extkey, sizeof(extkey));

                // normal kyber not 90s
                uint8_t tmp[504];
                Botan::SHA_3::finish(m_SHAKE256_RATE, spongeState, spongeStatePos, 0x1F, 0x80);
                Botan::SHA_3::expand(m_SHAKE256_RATE, spongeState, tmp, m_KYBER_ETA1*m_N/4 );

                secure_vector<uint8_t> buf_std(tmp, tmp + (m_KYBER_ETA1*m_N / 4));

                return buf_std;

                //shake256(out, outlen, extkey, sizeof(extkey));
            }
            else
            {
                // TODO 90s
                throw Not_Implemented("Kyber 90s is still TODO");
            }
        }


        /*************************************************
        * Name:        load32_littleendian
        *
        * Description: load 4 bytes into a 32-bit integer
        *              in little-endian order
        *
        * Arguments:   - const uint8_t *x: pointer to input byte array
        *
        * Returns 32-bit unsigned integer loaded from x
        **************************************************/
        uint32_t load32_littleendian(const uint8_t x[4])
        {
            uint32_t r;
            r = (uint32_t)x[0];
            r |= (uint32_t)x[1] << 8;
            r |= (uint32_t)x[2] << 16;
            r |= (uint32_t)x[3] << 24;
            return r;
        }

        /*************************************************
        * Name:        load24_littleendian
        *
        * Description: load 3 bytes into a 32-bit integer
        *              in little-endian order
        *              This function is only needed for Kyber-512
        *
        * Arguments:   - const uint8_t *x: pointer to input byte array
        *
        * Returns 32-bit unsigned integer loaded from x (most significant byte is zero)
        **************************************************/

        uint32_t load24_littleendian(const uint8_t x[3])
        {
            uint32_t r;
            r = (uint32_t)x[0];
            r |= (uint32_t)x[1] << 8;
            r |= (uint32_t)x[2] << 16;
            return r;
        }


        /*************************************************
        * Name:        cbd2
        *
        * Description: Given an array of uniformly random bytes, compute
        *              polynomial with coefficients distributed according to
        *              a centered binomial distribution with parameter eta=2
        *
        * Arguments:   - poly *r:                            pointer to output polynomial
        *              - const secure_vector<uint8_t>& buf: pointer to input byte array
        **************************************************/
        void cbd2(poly *r, const secure_vector<uint8_t>& buf)
        {
            if (buf.size() < (2 * m_N / 4))
            {
                throw std::runtime_error("Cannot cbd2 because buf incompatible buffer length!");
            }

            for (unsigned int i = 0;i<m_N / 8;i++) {
                uint32_t t = load32_littleendian(buf.data() + 4 * i);
                uint32_t d = t & 0x55555555;
                d += (t >> 1) & 0x55555555;

                for (unsigned int j = 0;j<8;j++) {
                    int16_t a = (d >> (4 * j + 0)) & 0x3;
                    int16_t b = (d >> (4 * j + 2)) & 0x3;
                    r->coeffs[8 * i + j] = a - b;
                }
            }
        }

        /*************************************************
        * Name:        cbd3
        *
        * Description: Given an array of uniformly random bytes, compute
        *              polynomial with coefficients distributed according to
        *              a centered binomial distribution with parameter eta=3
        *              This function is only needed for Kyber-512
        *
        * Arguments:   - poly *r:            pointer to output polynomial
        *              - const uint8_t *buf: pointer to input byte array
        **************************************************/
        void cbd3(poly *r, const secure_vector<uint8_t>& buf) // TODO bufLength   uint8_t buf[3 * m_N / 4]
        {

            if (buf.size() < (3 * m_N / 4))
            {
                throw std::runtime_error("Cannot cbd3 because buf incompatible buffer length!");
            }
            for (unsigned int i = 0;i<m_N / 4;i++) {
                uint32_t t = load24_littleendian(buf.data() + 3 * i);
                uint32_t d = t & 0x00249249;
                d += (t >> 1) & 0x00249249;
                d += (t >> 2) & 0x00249249;

                for (unsigned int j = 0;j<4;j++) {
                    int16_t a = (d >> (6 * j + 0)) & 0x7;
                    int16_t b = (d >> (6 * j + 3)) & 0x7;
                    r->coeffs[4 * i + j] = a - b;
                }
            }
        }


    void cbd_eta1(poly *r, const secure_vector<uint8_t>& buf) // TODO buf[m_KYBER_ETA1*m_N / 4]
    {
        if (buf.size() < (m_KYBER_ETA1*m_N / 4))
        {
            throw std::runtime_error("Cannot cbd_eta1 because incompatible buffer length!");
        }
        if (m_KYBER_ETA1 == 2)
        {
            cbd2(r, buf);
        }
        else if (m_KYBER_ETA1 == 3)
        {
            cbd3(r, buf);
        }
        else
        {
            throw std::runtime_error("This implementation requires eta1 in {2,3}");
        }
    }

    void cbd_eta2(poly *r, const secure_vector<uint8_t>& buf )
    {
        if (buf.size() < (m_KYBER_ETA2*m_N / 4))
        {
            throw std::runtime_error("Cannot cbd_eta2 because incompatible buffer length!");
        }
        if (m_KYBER_ETA2 != 2)
        {
            std::runtime_error("This implementation requires eta2 = 2");
        }

        cbd2(r, buf);
    }

        /*************************************************
        * Name:        poly_frommsg
        *
        * Description: Convert 32-byte message to polynomial
        *
        * Arguments:   - poly *r:            pointer to output polynomial
        *              - const uint8_t *msg: pointer to input message
        **************************************************/
    void poly_frommsg(poly *r, const uint8_t msg[], size_t msgLength)
    {
        unsigned int i, j;
        int16_t mask;

        if (msgLength != m_N / 8)
        {
            throw std::runtime_error("KYBER_INDCPA_MSGBYTES must be equal to KYBER_N/8 bytes!");
        }

            for (i = 0;i<m_N / 8;i++) {
                for (j = 0;j<8;j++) {
                    mask = -(int16_t)((msg[i] >> j) & 1);
                    r->coeffs[8 * i + j] = mask & ((m_Q + 1) / 2);
                }
            }
        }

        /*************************************************
        * Name:        poly_getnoise_eta2
        *
        * Description: Sample a polynomial deterministically from a seed and a nonce,
        *              with output polynomial close to centered binomial distribution
        *              with parameter KYBER_ETA2
        *
        * Arguments:   - poly *r:             pointer to output polynomial
        *              - const uint8_t *seed: pointer to input seed
        *                                     (of length KYBER_SYMBYTES bytes)
        *              - uint8_t nonce:       one-byte input nonce
        **************************************************/
        void poly_getnoise_eta2(poly *r, const uint8_t seed[32], uint8_t nonce)
        {
            auto buf = prf( seed, nonce);

            cbd_eta2(r, buf);
        }

        /*************************************************
        * Name:        poly_getnoise_eta1
        *
        * Description: Sample a polynomial deterministically from a seed and a nonce,
        *              with output polynomial close to centered binomial distribution
        *              with parameter KYBER_ETA1
        *
        * Arguments:   - poly *r:             pointer to output polynomial
        *              - const uint8_t *seed: pointer to input seed
        *                                     (of length KYBER_SYMBYTES bytes)
        *              - uint8_t nonce:       one-byte input nonce
        **************************************************/
        void poly_getnoise_eta1(poly *r, const uint8_t seed[32], uint8_t nonce)
        {
            auto buf = prf(seed, nonce);

            cbd_eta1(r, buf);
        }

        /*************************************************
        * Name:        indcpa_enc
        *
        * Description: Encryption function of the CPA-secure
        *              public-key encryption scheme underlying Kyber.
        *
        * Arguments:   - uint8_t *c:           pointer to output ciphertext
        *                                      (of length KYBER_INDCPA_BYTES bytes)
        *              - const uint8_t *m:     pointer to input message
        *                                      (of length KYBER_INDCPA_MSGBYTES bytes)
        *              - const uint8_t *pk:    pointer to input public key
        *                                      (of length KYBER_INDCPA_PUBLICKEYBYTES)
        *              - const uint8_t *coins: pointer to input random coins
        *                                      used as seed (of length KYBER_SYMBYTES)
        *                                      to deterministically generate all
        *                                      randomness
        *                                      TO DO XXX
        **************************************************/
        void indcpa_enc( secure_vector<uint8_t>& c,
            const uint8_t m[32], // TODO m [symbyts]
            const std::vector<uint8_t>& pk,
            const uint8_t coins[32] ) // TODO coins (symbytes)
        {
            unsigned int i;
            secure_vector<uint8_t> seed( get_sym_bytes() );
            uint8_t nonce = 0;
            polyvec sp, pkpv, ep, bp;
            poly v, k, epp;

            unpack_pk( &pkpv, seed, pk );
            poly_frommsg( &k, m , m_sym_bytes );
            const auto kyber_k = get_k();
            std::vector<polyvec> at( kyber_k );
            gen_matrix( at, seed, 1 );

            for ( i = 0; i < m_k; i++ )
                poly_getnoise_eta1( sp.vec + i, coins, nonce++ );
            for ( i = 0; i < m_k; i++ )
                poly_getnoise_eta2( ep.vec + i, coins, nonce++ );
            poly_getnoise_eta2( &epp, coins, nonce++ );

            polyvec_ntt( &sp );

            // matrix-vector multiplication
            for ( i = 0; i < m_k; i++ )
                polyvec_pointwise_acc_montgomery( &bp.vec[i], &at[i], &sp );

            polyvec_pointwise_acc_montgomery( &v, &pkpv, &sp );

            polyvec_invntt_tomont( &bp );
            poly_invntt_tomont( &v );

            polyvec_add( &bp, &bp, &ep );
            poly_add( &v, &v, &epp );
            poly_add( &v, &v, &k );
            polyvec_reduce( &bp );
            poly_reduce( &v );

            c.resize( m_ciphertext_bytes );
            pack_ciphertext( c, &bp, &v );
        }

        /*************************************************
        * Name:        poly_ntt
        *
        * Description: Computes negacyclic number-theoretic transform (NTT) of
        *              a polynomial in place;
        *              inputs assumed to be in normal order, output in bitreversed order
        *
        * Arguments:   - uint16_t *r: pointer to in/output polynomial
        **************************************************/
        void poly_ntt(poly *r)
        {
            ntt(r->coeffs);
            poly_reduce(r);
        }


        /*************************************************
        * Name:        poly_decompress
        *
        * Description: De-serialization and subsequent decompression of a polynomial;
        *              approximate inverse of poly_compress
        *
        * Arguments:   - poly *r:          pointer to output polynomial
        *              - const uint8_t *a: pointer to input byte array
        *                                  (of length KYBER_POLYCOMPRESSEDBYTES bytes)
        **************************************************/
        void poly_decompress(poly *r, const uint8_t a[], size_t aLength ) // TODO a[KYBER_POLYCOMPRESSEDBYTES]
        {
            unsigned int i;

            if (aLength == 128)
            {
                for (i = 0;i < m_N / 2;i++) {
                    r->coeffs[2 * i + 0] = (((uint16_t)(a[0] & 15)*m_Q) + 8) >> 4;
                    r->coeffs[2 * i + 1] = (((uint16_t)(a[0] >> 4)*m_Q) + 8) >> 4;
                    a += 1;
                }
            }
            else if(aLength == 160)
            {
                unsigned int j;
                uint8_t t[8];
                for (i = 0;i < m_N / 8;i++) {
                    t[0] = (a[0] >> 0);
                    t[1] = (a[0] >> 5) | (a[1] << 3);
                    t[2] = (a[1] >> 2);
                    t[3] = (a[1] >> 7) | (a[2] << 1);
                    t[4] = (a[2] >> 4) | (a[3] << 4);
                    t[5] = (a[3] >> 1);
                    t[6] = (a[3] >> 6) | (a[4] << 2);
                    t[7] = (a[4] >> 3);
                    a += 5;

                    for (j = 0;j < 8;j++)
                        r->coeffs[8 * i + j] = ((uint32_t)(t[j] & 31)*m_Q + 16) >> 5;
                }
            }
            else
            {
                throw std::runtime_error("KYBER_POLYCOMPRESSEDBYTES needs to be in {128, 160}");
            }
        }
        /*************************************************
        * Name:        unpack_ciphertext
        *
        * Description: De-serialize and decompress ciphertext from a byte array;
        *              approximate inverse of pack_ciphertext
        *
        * Arguments:   - polyvec *b:       pointer to the output vector of polynomials b
        *              - poly *v:          pointer to the output polynomial v
        *              - const uint8_t *c: pointer to the input serialized ciphertext
        **************************************************/
        void unpack_ciphertext( polyvec* b,
            poly* v,
            const uint8_t* c, size_t c_len )
        {
            polyvec_decompress( b, c, c_len );
            poly_decompress( v, c + m_poly_vec_compressed_bytes, m_poly_compressed_bytes);
        }

        /*************************************************
        * Name:        polyvec_ntt
        *
        * Description: Apply forward NTT to all elements of a vector of polynomials
        *
        * Arguments:   - polyvec *r: pointer to in/output vector of polynomials
        **************************************************/
        void polyvec_ntt(polyvec *r)
        {
            unsigned int i;
            for (i = 0;i<m_k;i++)
                poly_ntt(&r->vec[i]);
        }

        /*************************************************
        * Name:        montgomery_reduce
        *
        * Description: Montgomery reduction; given a 32-bit integer a, computes
        *              16-bit integer congruent to a * R^-1 mod q,
        *              where R=2^16
        *
        * Arguments:   - int32_t a: input integer to be reduced;
        *                           has to be in {-q2^15,...,q2^15-1}
        *
        * Returns:     integer in {-q+1,...,q-1} congruent to a * R^-1 modulo q.
        **************************************************/
        int16_t montgomery_reduce(int32_t a)
        {
            int32_t t;
            int16_t u;

            u = a*m_Q_inv;
            t = (int32_t)u*m_Q;
            t = a - t;
            t >>= 16;
            return t;
        }
        /*************************************************
        * Name:        fqmul
        *
        * Description: Multiplication followed by Montgomery reduction
        *
        * Arguments:   - int16_t a: first factor
        *              - int16_t b: second factor
        *
        * Returns 16-bit integer congruent to a*b*R^{-1} mod q
        **************************************************/
        int16_t fqmul(int16_t a, int16_t b) {
            return montgomery_reduce((int32_t)a*b);
        }
        /*************************************************
        * Name:        basemul
        *
        * Description: Multiplication of polynomials in Zq[X]/(X^2-zeta)
        *              used for multiplication of elements in Rq in NTT domain
        *
        * Arguments:   - int16_t r[2]:       pointer to the output polynomial
        *              - const int16_t a[2]: pointer to the first factor
        *              - const int16_t b[2]: pointer to the second factor
        *              - int16_t zeta:       integer defining the reduction polynomial
        **************************************************/
        void basemul(int16_t r[2],
            const int16_t a[2],
            const int16_t b[2],
            int16_t zeta)
        {
            r[0] = fqmul(a[1], b[1]);
            r[0] = fqmul(r[0], zeta);
            r[0] += fqmul(a[0], b[0]);

            r[1] = fqmul(a[0], b[1]);
            r[1] += fqmul(a[1], b[0]);
        }


        /*************************************************
        * Name:        poly_basemul_montgomery
        *
        * Description: Multiplication of two polynomials in NTT domain
        *
        * Arguments:   - poly *r:       pointer to output polynomial
        *              - const poly *a: pointer to first input polynomial
        *              - const poly *b: pointer to second input polynomial
        **************************************************/
        void poly_basemul_montgomery(poly *r, const poly *a, const poly *b)
        {
            unsigned int i;
            for (i = 0;i<m_N/ 4;i++) {
                basemul(&r->coeffs[4 * i], &a->coeffs[4 * i], &b->coeffs[4 * i], zetas[64 + i]);
                basemul(&r->coeffs[4 * i + 2], &a->coeffs[4 * i + 2], &b->coeffs[4 * i + 2],
                    -zetas[64 + i]);
            }
        }
        /*************************************************
        * Name:        polyvec_pointwise_acc_montgomery
        *
        * Description: Pointwise multiply elements of a and b, accumulate into r,
        *              and multiply by 2^-16.
        *
        * Arguments: - poly *r:          pointer to output polynomial
        *            - const polyvec *a: pointer to first input vector of polynomials
        *            - const polyvec *b: pointer to second input vector of polynomials
        **************************************************/
        void polyvec_pointwise_acc_montgomery(poly *r,
            const polyvec *a,
            const polyvec *b)
        {
            unsigned int i;
            poly t;

            poly_basemul_montgomery(r, &a->vec[0], &b->vec[0]);
            for (i = 1;i<m_k;i++) {
                poly_basemul_montgomery(&t, &a->vec[i], &b->vec[i]);
                poly_add(r, r, &t);
            }

            poly_reduce(r);
        }


        /*************************************************
        * Name:        barrett_reduce
        *
        * Description: Barrett reduction; given a 16-bit integer a, computes
        *              16-bit integer congruent to a mod q in {0,...,q}
        *
        * Arguments:   - int16_t a: input integer to be reduced
        *
        * Returns:     integer in {0,...,q} congruent to a modulo q.
        **************************************************/
        int16_t barrett_reduce(int16_t a) {
            int16_t t;
            const int16_t v = ((1U << 26) + m_Q/ 2) / m_Q;

            t = (int32_t)v*a >> 26;
            t *= m_Q;
            return a - t;
        }
        /*************************************************
        * Name:        invntt_tomont
        *
        * Description: Inplace inverse number-theoretic transform in Rq and
        *              multiplication by Montgomery factor 2^16.
        *              Input is in bitreversed order, output is in standard order
        *
        * Arguments:   - int16_t r[256]: pointer to input/output vector of elements
        *                                of Zq
        **************************************************/
        void invntt(int16_t r[256]) {
            unsigned int start, len, j, k;
            int16_t t, zeta;

            k = 0;
            for (len = 2; len <= 128; len <<= 1) {
                for (start = 0; start < 256; start = j + len) {
                    zeta = zetas_inv[k++];
                    for (j = start; j < start + len; ++j) {
                        t = r[j];
                        r[j] = barrett_reduce(t + r[j + len]);
                        r[j + len] = t - r[j + len];
                        r[j + len] = fqmul(zeta, r[j + len]);
                    }
                }
            }

            for (j = 0; j < 256; ++j)
                r[j] = fqmul(r[j], zetas_inv[127]);
        }

        /*************************************************
        * Name:        poly_invntt_tomont
        *
        * Description: Computes inverse of negacyclic number-theoretic transform (NTT)
        *              of a polynomial in place;
        *              inputs assumed to be in bitreversed order, output in normal order
        *
        * Arguments:   - uint16_t *a: pointer to in/output polynomial
        **************************************************/
        void poly_invntt_tomont(poly *r)
        {
            invntt(r->coeffs);
        }


        /*************************************************
        * Name:        ntt
        *
        * Description: Inplace number-theoretic transform (NTT) in Rq
        *              input is in standard order, output is in bitreversed order
        *
        * Arguments:   - int16_t r[256]: pointer to input/output vector of elements
        *                                of Zq
        **************************************************/
        void ntt(int16_t r[256]) {
            unsigned int len, start, j, k;
            int16_t t, zeta;

            k = 1;
            for (len = 128; len >= 2; len >>= 1) {
                for (start = 0; start < 256; start = j + len) {
                    zeta = zetas[k++];
                    for (j = start; j < start + len; ++j) {
                        t = fqmul(zeta, r[j + len]);
                        r[j + len] = r[j] - t;
                        r[j] = r[j] + t;
                    }
                }
            }
        }


        /*************************************************
        * Name:        poly_sub
        *
        * Description: Subtract two polynomials
        *
        * Arguments: - poly *r:       pointer to output polynomial
        *            - const poly *a: pointer to first input polynomial
        *            - const poly *b: pointer to second input polynomial
        **************************************************/
        void poly_sub(poly *r, const poly *a, const poly *b)
        {
            unsigned int i;
            for (i = 0;i<m_N;i++)
                r->coeffs[i] = a->coeffs[i] - b->coeffs[i];
        }


        /*************************************************
        * Name:        poly_reduce
        *
        * Description: Applies Barrett reduction to all coefficients of a polynomial
        *              for details of the Barrett reduction see comments in reduce.c
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void poly_reduce(poly *r)
        {
            unsigned int i;
            for (i = 0;i<m_N;i++)
                r->coeffs[i] = barrett_reduce(r->coeffs[i]);
        }


        /*************************************************
        * Name:        poly_tomsg
        *
        * Description: Convert polynomial to 32-byte message
        *
        * Arguments:   - uint8_t *msg: pointer to output message
        *              - poly *a:      pointer to input polynomial
        **************************************************/
        void poly_tomsg(uint8_t msg[32], poly *a)  // TODO msg [ symbytes]
        {
            unsigned int i, j;
            uint16_t t;

            poly_csubq(a);

            for (i = 0;i<m_N / 8;i++) {
                msg[i] = 0;
                for (j = 0;j<8;j++) {
                    t = ((((uint16_t)a->coeffs[8 * i + j] << 1) + m_Q / 2) / m_Q) & 1;
                    msg[i] |= t << j;
                }
            }
        }

        /*************************************************
        * Name:        indcpa_dec
        *
        * Description: Decryption function of the CPA-secure
        *              public-key encryption scheme underlying Kyber.
        *
        * Arguments:   - uint8_t *m:        pointer to output decrypted message
        *                                   (of length KYBER_INDCPA_MSGBYTES)
        *              - const uint8_t *c:  pointer to input ciphertext
        *                                   (of length KYBER_INDCPA_BYTES)
        *              - const uint8_t *sk: pointer to input secret key
        *                                   (of length KYBER_INDCPA_SECRETKEYBYTES)
        **************************************************/
        void indcpa_dec( uint8_t m[32],  // TODO m[symbytes]
            const uint8_t* c, size_t c_len,
            const std::vector<uint8_t>& sk )
        {
            polyvec bp, skpv;
            poly v, mp;

            unpack_ciphertext( &bp, &v, c, c_len );
            unpack_sk( &skpv, sk );

            polyvec_ntt( &bp );
            polyvec_pointwise_acc_montgomery( &mp, &skpv, &bp );
            poly_invntt_tomont( &mp );

            poly_sub( &mp, &v, &mp );
            poly_reduce( &mp );

            poly_tomsg( m, &mp );
        }



        /*************************************************
        * Name:        kyber_indcpa_keypair
        *
        * Description: Generates public and private key for the CPA-secure
        *              public-key encryption scheme underlying Kyber
        *
        * Arguments:   - uint8_t *pk: pointer to output public key
        *                             (of length KYBER_INDCPA_PUBLICKEYBYTES bytes)
        *              - uint8_t *sk: pointer to output private key
                                      (of length KYBER_INDCPA_SECRETKEYBYTES bytes)
        **************************************************/
        void kyber_indcpa_keypair( std::vector<uint8_t>& pk, secure_vector<uint8_t>& sk, RandomNumberGenerator& rng, KyberMode mode )
        {
            Kyber_Internal_Operation kyberIntOps( mode );

            unsigned int i;
            constexpr static auto rand_size = 32;
            byte rand[rand_size];
            uint8_t nonce = 0;
            const auto kyber_k = kyberIntOps.get_k();
            std::vector<polyvec> a( kyber_k );
            polyvec e, pkpv, skpv;

            rng.randomize( rand, rand_size );
            std::unique_ptr<HashFunction> hash3( HashFunction::create( "SHA-3(512)" ) );
            hash3->update( rand, rand_size );
            auto seed = hash3->final();

            kyberIntOps.gen_matrix( a, seed, 0 );

            for ( i = 0; i < kyber_k; i++ )
                poly_getnoise_eta1( &skpv.vec[i], seed.data() + 32, nonce++ );
            for ( i = 0; i < kyber_k; i++ )
                poly_getnoise_eta1( &e.vec[i], seed.data() + 32, nonce++ );

            polyvec_ntt( &skpv );
            polyvec_ntt( &e );

            // matrix-vector multiplication
            for ( i = 0; i < kyber_k; i++ ) {
                polyvec_pointwise_acc_montgomery( &pkpv.vec[i], &a.at( i ), &skpv );
                poly_tomont( &pkpv.vec[i] );
            }

            polyvec_add( &pkpv, &pkpv, &e );
            polyvec_reduce( &pkpv );

            polyvec_tobytes( sk, &skpv );
            polyvec_tobytes( pk, &pkpv );
            for ( i = 0; i < kyberIntOps.get_sym_bytes(); i++ )
                pk[i + kyberIntOps.get_poly_vec_bytes()] = seed.at( i );
        }

        Kyber_Internal_Operation( KyberMode mode )
        {
            if ( mode == KyberMode::Kyber512 )
            {
                m_k = 2;
                m_poly_vec_compressed_bytes = m_k * 320;
                m_poly_compressed_bytes = 128;
                m_KYBER_ETA1 = 3;
            }
            else if ( mode == KyberMode::Kyber768 )
            {
                m_k = 3;
                m_poly_vec_compressed_bytes = m_k * 320;
                m_poly_compressed_bytes = 128;
                m_KYBER_ETA1 = 2;
            }
            else if ( mode == KyberMode::Kyber1024 )
            {
                m_k = 4;
                m_poly_vec_compressed_bytes = m_k * 352;
                m_poly_compressed_bytes = 160;
                m_KYBER_ETA1 = 2;
            }
            else
            {
                throw std::runtime_error( "invalid kyber mode" );
            }

            m_poly_vec_bytes = m_k * m_poly_bytes;
            m_public_key_bytes = m_poly_vec_bytes + m_sym_bytes;
            m_secret_key_bytes = m_poly_vec_bytes + m_public_key_bytes + 2 * m_sym_bytes;
            m_ciphertext_bytes = m_poly_vec_compressed_bytes + m_poly_compressed_bytes;
            m_gen_matrix_nblocks = ((12 * m_N / 8 * (1 << 12) / m_Q \
                + m_XOF_BLOCKBYTES) / m_XOF_BLOCKBYTES);
        }

        size_t get_public_key_bytes() const { return m_public_key_bytes; }
        size_t get_poly_vec_bytes() const { return m_poly_vec_bytes; }
        size_t get_poly_bytes() const { return m_poly_bytes; }
        size_t get_secret_key_bytes() const { return m_secret_key_bytes; }
        size_t get_sym_bytes() const { return m_sym_bytes; }
        size_t get_ciphertext_bytes() const { return m_ciphertext_bytes; }
        size_t get_k() const { return m_k; }
        size_t get_n() const { return m_N; }


        /*************************************************
        * Name:        rej_uniform
        *
        * Description: Run rejection sampling on uniform random bytes to generate
        *              uniform random integers mod q
        *
        * Arguments:   - int16_t *r:          pointer to output buffer
        *              - unsigned int len:    requested number of 16-bit integers
        *                                     (uniform mod q)
        *              - const uint8_t *buf:  pointer to input buffer
        *                                     (assumed to be uniform random bytes)
        *              - unsigned int buflen: length of input buffer in bytes
        *
        * Returns number of sampled 16-bit integers (at most len)
        **************************************************/
        unsigned int rej_uniform(int16_t* r,
            unsigned int len,
            const uint8_t* buf,
            unsigned int buflen)
        {
            unsigned int ctr, pos;
            uint16_t val0, val1;

            ctr = pos = 0;
            while (ctr < len && pos + 3 <= buflen) {
                val0 = ((buf[pos + 0] >> 0) | ((uint16_t)buf[pos + 1] << 8)) & 0xFFF;
                val1 = ((buf[pos + 1] >> 4) | ((uint16_t)buf[pos + 2] << 4)) & 0xFFF;
                pos += 3;

                if (val0 < m_Q)
                    r[ctr++] = val0;
                if (ctr < len && val1 < m_Q)
                    r[ctr++] = val1;
            }

            return ctr;
        }


    /*************************************************
    * Name:        gen_matrix
    *
    * Description: Deterministically generate matrix A (or the transpose of A)
    *              from a seed. Entries of the matrix are polynomials that look
    *              uniformly random. Performs rejection sampling on output of
    *              a XOF
    *
    * Arguments:   - polyvec std::vector a:     vector to ouptput matrix A
    *              - const std::vector seed:    vector to input seed
    *              - int transposed:            boolean deciding whether A or A^T
    *                                           is generated
    **************************************************/

    // Not static for benchmarking
    void gen_matrix(std::vector<polyvec>& a, const secure_vector<uint8_t>& seed, int transposed)
    {
        unsigned int ctr, i, j, k;
        unsigned int buflen, off;

        for (i = 0; i < m_k; i++) {
            for (j = 0; j < m_k; j++) {

                secure_vector< uint64_t > spongeState;
                spongeState.resize(25);
                size_t spongeStatePos = 0;
                if (transposed)
                {
                    // TODO 90s variant uses aes
                    unsigned int h;
                    uint8_t extseed1[m_sym_bytes + 2];

                    for (h = 0;h < m_sym_bytes;h++)
                    {
                        extseed1[h] = seed[h];
                    }
                    extseed1[h++] = i;
                    extseed1[h] = j;

                    // normal kyber not 90s

                    spongeStatePos = Botan::SHA_3::absorb(m_SHAKE128_RATE, spongeState, spongeStatePos, extseed1, m_sym_bytes + 2);

                }
                else
                {
                    unsigned int h;
                    uint8_t extseed1[m_sym_bytes + 2];

                    for (h = 0;h < m_sym_bytes;h++)
                    {
                        extseed1[h] = seed[h];
                    }
                    extseed1[h++] = j;
                    extseed1[h] = i;

                    // normal kyber not 90s
                    spongeStatePos = Botan::SHA_3::absorb(m_SHAKE128_RATE, spongeState, spongeStatePos, extseed1, m_sym_bytes + 2);

                }

                // normal kyber not 90s
                uint8_t tmp[504];
                Botan::SHA_3::finish(m_SHAKE128_RATE, spongeState, spongeStatePos, 0x1F, 0x80);
                Botan::SHA_3::expand(m_SHAKE128_RATE, spongeState, tmp, 504);

                std::vector <uint8_t> buf_std(tmp, tmp + (m_gen_matrix_nblocks * m_XOF_BLOCKBYTES + 2));

                buflen = m_gen_matrix_nblocks * m_XOF_BLOCKBYTES;
                ctr = rej_uniform(a[i].vec[j].coeffs, m_N, buf_std.data(), buflen);

                while (ctr < m_N) {
                    off = buflen % 3;
                    for (k = 0; k < off; k++)
                        buf_std[k] = buf_std[buflen - off + k];


                    // normal kyber not 90s
                    Botan::SHA_3::finish(m_SHAKE128_RATE, spongeState, spongeStatePos, 0x1F, 0x80);
                    Botan::SHA_3::expand(m_SHAKE128_RATE, spongeState, tmp + off, 200);


                    buflen = off + m_XOF_BLOCKBYTES;
                    ctr += rej_uniform(a[i].vec[j].coeffs + ctr, m_N - ctr, buf_std.data(), buflen);
                }
            }
        }
    }

    private:
        constexpr static size_t m_N = 256;
        constexpr static size_t m_Q = 3329;

        constexpr static size_t m_sym_bytes = 32;
        constexpr static size_t m_ss_bytes = 32;

        constexpr static size_t m_poly_bytes = 384;

        constexpr static size_t m_ETA2 = 2;
        constexpr static size_t m_Q_inv = 62209; // q^-1 mod 2^16
        constexpr static size_t m_XOF_BLOCKBYTES = 168; // SHAKE128 Rate
        constexpr static size_t m_SHAKE256_RATE = 136*8; // shake absorb rate
        constexpr static size_t m_SHAKE128_RATE = 168*8;
        constexpr static size_t m_KYBER_ETA2 = 2;

        const int16_t zetas[128] = {
          2285, 2571, 2970, 1812, 1493, 1422, 287, 202, 3158, 622, 1577, 182, 962,
          2127, 1855, 1468, 573, 2004, 264, 383, 2500, 1458, 1727, 3199, 2648, 1017,
          732, 608, 1787, 411, 3124, 1758, 1223, 652, 2777, 1015, 2036, 1491, 3047,
          1785, 516, 3321, 3009, 2663, 1711, 2167, 126, 1469, 2476, 3239, 3058, 830,
          107, 1908, 3082, 2378, 2931, 961, 1821, 2604, 448, 2264, 677, 2054, 2226,
          430, 555, 843, 2078, 871, 1550, 105, 422, 587, 177, 3094, 3038, 2869, 1574,
          1653, 3083, 778, 1159, 3182, 2552, 1483, 2727, 1119, 1739, 644, 2457, 349,
          418, 329, 3173, 3254, 817, 1097, 603, 610, 1322, 2044, 1864, 384, 2114, 3193,
          1218, 1994, 2455, 220, 2142, 1670, 2144, 1799, 2051, 794, 1819, 2475, 2459,
          478, 3221, 3021, 996, 991, 958, 1869, 1522, 1628
        };

        const int16_t zetas_inv[128] = {
            1701, 1807, 1460, 2371, 2338, 2333, 308, 108, 2851, 870, 854, 1510, 2535,
            1278, 1530, 1185, 1659, 1187, 3109, 874, 1335, 2111, 136, 1215, 2945, 1465,
            1285, 2007, 2719, 2726, 2232, 2512, 75, 156, 3000, 2911, 2980, 872, 2685,
            1590, 2210, 602, 1846, 777, 147, 2170, 2551, 246, 1676, 1755, 460, 291, 235,
            3152, 2742, 2907, 3224, 1779, 2458, 1251, 2486, 2774, 2899, 1103, 1275, 2652,
            1065, 2881, 725, 1508, 2368, 398, 951, 247, 1421, 3222, 2499, 271, 90, 853,
            1860, 3203, 1162, 1618, 666, 320, 8, 2813, 1544, 282, 1838, 1293, 2314, 552,
            2677, 2106, 1571, 205, 2918, 1542, 2721, 2597, 2312, 681, 130, 1602, 1871,
            829, 2946, 3065, 1325, 2756, 1861, 1474, 1202, 2367, 3147, 1752, 2707, 171,
            3127, 3042, 1907, 1836, 1517, 359, 758, 1441
        };
        size_t m_k;
        size_t m_poly_vec_bytes;
        size_t m_poly_vec_compressed_bytes;
        size_t m_poly_compressed_bytes;
        size_t m_public_key_bytes;
        size_t m_secret_key_bytes;
        size_t m_ciphertext_bytes;
        size_t m_gen_matrix_nblocks;
        size_t m_KYBER_ETA1;
        bool m_kyber_90s = false;
    };
}

namespace Botan
{

    class Kyber_KEM_Encryptor final : public PK_Ops::KEM_Encryption
    {
    public:

        Kyber_KEM_Encryptor(const Kyber_PublicKey& key) :
            KEM_Encryption(), m_key(key) {}

        void kem_encrypt(secure_vector<uint8_t>& out_encapsulated_key,
            secure_vector<uint8_t>& out_shared_key,
            size_t desired_shared_key_len,
            RandomNumberGenerator& rng,
            const uint8_t salt[],
            size_t salt_len) override
        {
            BOTAN_UNUSED(salt, salt_len);

            secure_vector<uint8_t> plaintext;
            plaintext.resize(desired_shared_key_len);
            secure_vector<uint8_t> ciphertext;

            kyber_encrypt(ciphertext, plaintext, m_key.public_key_bits(), rng);

            out_shared_key.swap(plaintext);
            out_encapsulated_key.swap(ciphertext);
        }

    private:

        void kyber_encrypt(secure_vector<uint8_t>& ct,
            secure_vector<uint8_t>& sharedSecret,
            const std::vector<uint8_t>& pk, RandomNumberGenerator& rng)
        {
            Kyber_Internal_Operation kyber_internal( m_key.get_mode() );
            auto sym_bytes = kyber_internal.get_sym_bytes();
            secure_vector<uint8_t> buf( sym_bytes );
            rng.randomize( buf.data(), buf.size() );
            /* Don't release system RNG output */

            std::unique_ptr<HashFunction> sha3_256_botan(HashFunction::create("SHA-3(256)"));
            std::unique_ptr<HashFunction> sha3_512_botan(HashFunction::create("SHA-3(512)"));
            std::unique_ptr<HashFunction> shake_256_botan(HashFunction::create("SHAKE-256"));

            secure_vector<uint8_t> secBuf;
            secure_vector<uint8_t> secKr;

            sha3_256_botan->update(buf);
            secBuf = sha3_256_botan->final();

            // Multitarget countermeasure for coins + contributory KEM
            sha3_256_botan->update(pk);
            auto tmp = sha3_256_botan->final();
            secBuf.insert(secBuf.end(), tmp.begin(), tmp.end());

            sha3_512_botan->update(secBuf);
            secKr = sha3_512_botan->final();

            // coins are in kr+KYBER_SYMBYTES
            kyber_internal.indcpa_enc(ct, secBuf.data(), pk, secKr.data() + sym_bytes );

            // overwrite coins in kr with H(c)
            sha3_256_botan->update(ct);
            tmp = sha3_256_botan->final();

            std::copy(tmp.begin(), tmp.end(), secKr.begin() + sym_bytes);

            // hash concatenation of pre-k and H(c) to k
            shake_256_botan->update(secKr.data(), 2 * sym_bytes );
            sharedSecret = shake_256_botan->final();
        }

        const Kyber_PublicKey& m_key;
    };

    class Kyber_KEM_Decryptor final : public PK_Ops::KEM_Decryption
    {
    public:

        Kyber_KEM_Decryptor(const Kyber_PrivateKey& key) :
            KEM_Decryption(), m_key(key) {}

        secure_vector<uint8_t> kem_decrypt(const uint8_t encap_key[],
            size_t len_encap_key,
            size_t desired_shared_key_len,
            const uint8_t salt[],
            size_t salt_len) override
        {
            BOTAN_UNUSED(salt, salt_len);

            secure_vector<uint8_t> plaintext;
            plaintext.resize(desired_shared_key_len);
            kyber_decrypt(plaintext, encap_key, len_encap_key, m_key.private_key_bits());

            return plaintext;
        }

    private:

        void kyber_decrypt(secure_vector<uint8_t>& ss,
            const uint8_t* ct, size_t ct_len,
            secure_vector<uint8_t> sk)
        {
            size_t i;
            int fail;
            uint8_t buf[2 * 32];
            const auto sk_unlocked = unlock(sk);
            const auto sk_data = sk_unlocked.data();
            Kyber_Internal_Operation kyber_internal( m_key.get_mode() );
            const std::vector<uint8_t> pk( sk_unlocked.begin() + kyber_internal.get_poly_vec_bytes(), sk_unlocked.end() );

            std::unique_ptr<HashFunction> sha3_256_botan(HashFunction::create("SHA-3(256)"));
            std::unique_ptr<HashFunction> sha3_512_botan(HashFunction::create("SHA-3(512)"));
            std::unique_ptr<HashFunction> shake_256_botan(HashFunction::create("SHAKE-256"));

            secure_vector<uint8_t> secBuf;
            secure_vector<uint8_t> secKr;

            kyber_internal.indcpa_dec(buf, ct, ct_len, sk_unlocked );
            // Use secBuf. Insert data from buf
            const auto sym_bytes = kyber_internal.get_sym_bytes();
            secBuf.insert(secBuf.begin(), buf, buf + 2 * sym_bytes);

            /* Multitarget countermeasure for coins + contributory KEM */
            const auto secret_key_bytes = kyber_internal.get_secret_key_bytes();
            for (i = 0; i < sym_bytes; i++)
            {
                secBuf.at(sym_bytes + i) = sk_unlocked.at( secret_key_bytes - 2 * sym_bytes + i);
            }
            sha3_512_botan->update(secBuf);
            secKr = sha3_512_botan->final();

            /* coins are in kr+KYBER_SYMBYTES */
            secure_vector<uint8_t> cmp;
            kyber_internal.indcpa_enc(cmp, secBuf.data(), pk, secKr.data() + sym_bytes );

            const auto ciphertext_bytes = kyber_internal.get_ciphertext_bytes();
            fail = !constant_time_compare(ct, cmp.data(), ciphertext_bytes);

            /* overwrite coins in kr with H(c) */
            sha3_256_botan->update(ct, ciphertext_bytes );
            auto tmp = sha3_256_botan->final();
            secure_vector<uint8_t> secKrFinal{ secKr.begin(), secKr.begin() + sym_bytes };
            secKrFinal.insert(secKrFinal.end(),tmp.begin(),tmp.end());

            secure_vector<uint8_t> secKrFinalFail( sk_data + secret_key_bytes - sym_bytes, sk_data + secret_key_bytes);
            /* hash concatenation of pre-k and H(c) to k */
            /* Overwrite pre-k with z on re-encryption failure */
            fail ? sha3_256_botan->update(secKrFinalFail) : shake_256_botan->update(secKrFinal);
            ss = shake_256_botan->final();
        }

        const Kyber_PrivateKey& m_key;
    };

    std::string Kyber_PublicKey::algo_name() const
    {
        return "kyber-r3";
    }

    AlgorithmIdentifier Kyber_PublicKey::algorithm_identifier() const
    {
        return AlgorithmIdentifier(get_oid(), AlgorithmIdentifier::USE_EMPTY_PARAM);
    }

    size_t Kyber_PublicKey::estimated_strength() const
    {
        /* NIST Strength 1 - Kyber512 - AES 128
         * NIST Strenght 3 - Kyber 768 - AES 192
         * NIST Strenght 5 - Kyber 1024 - AES 256
         */
        switch (m_kyber_mode)
         {
         case KyberMode::Kyber512:
             return 128;
             break;
         case KyberMode::Kyber768:
             return 192;
             break;
         case KyberMode::Kyber1024:
             return 256;
             break;
         default:
             return 0;
         }
    }

    Kyber_PublicKey::Kyber_PublicKey( const std::vector<uint8_t>& pub_key, KyberMode mode ) :
        m_kyber_mode( mode ), m_public_key( pub_key ) {}

    std::vector<uint8_t> Kyber_PublicKey::public_key_bits() const
    {
        return m_public_key;
    }

    size_t Kyber_PublicKey::key_length() const { return m_public_key.size(); };

    KyberMode Kyber_PublicKey::get_mode() const { return m_kyber_mode; }

    bool Kyber_PublicKey::check_key( RandomNumberGenerator& rng, bool ) const
    {
        bool result = true;
        try
        {
            PK_KEM_Encryptor encryptor_bob( *this, rng );

            secure_vector<uint8_t> cipher_text, key_bob;
            encryptor_bob.encrypt( cipher_text, key_bob, 32, rng );
        }
        catch ( ... )
        {
            result = false;
        }

        return result;
    }

    Kyber_PrivateKey::Kyber_PrivateKey( RandomNumberGenerator& rng, KyberMode mode )
    {
        *this = generate_kyber_key(rng, mode);
    }

    Kyber_PrivateKey::Kyber_PrivateKey( secure_vector<uint8_t> sk, std::vector<uint8_t> pk, KyberMode mode ): Kyber_PublicKey(pk, mode),  m_sk( sk )
    {    }

    Kyber_PrivateKey Kyber_PrivateKey::generate_kyber_key(RandomNumberGenerator& rng, KyberMode mode)
    {
        Kyber_Internal_Operation kyber_internal( mode );
        std::vector<uint8_t> pk( kyber_internal.get_public_key_bytes() );
        secure_vector<uint8_t> sk( kyber_internal.get_secret_key_bytes() );

        kyber_internal.kyber_indcpa_keypair(pk, sk, rng, mode);

        const auto public_key_bytes = kyber_internal.get_public_key_bytes();
        const auto poly_vec_bytes = kyber_internal.get_poly_vec_bytes();
        for (size_t i = 0; i < public_key_bytes; i++)
            sk[i + poly_vec_bytes] = pk[i];

        std::unique_ptr<HashFunction> hash3(HashFunction::create("SHA-3(256)"));
        hash3->update(pk.data(), public_key_bytes);
        auto hash_output = hash3->final();

        const auto secret_key_bytes = kyber_internal.get_secret_key_bytes();
        const auto sym_bytes = kyber_internal.get_sym_bytes();

        std::copy(hash_output.begin(), hash_output.end(), sk.begin() + secret_key_bytes - 2 * sym_bytes);
        /* Value z for pseudo-random output on reject */
        rng.randomize(sk.data() + secret_key_bytes - sym_bytes, sym_bytes);

        return Kyber_PrivateKey(sk, pk, mode);
    }

    secure_vector<uint8_t> Kyber_PrivateKey::private_key_bits() const
    {
        return m_sk;
    }

    std::unique_ptr<PK_Ops::KEM_Encryption>
        Kyber_PublicKey::create_kem_encryption_op(RandomNumberGenerator& rng,
            const std::string& params,
            const std::string& provider) const
    {
        BOTAN_UNUSED(rng, params);

        if (provider == "base" || provider.empty())
            return std::unique_ptr<PK_Ops::KEM_Encryption>(new Kyber_KEM_Encryptor(*this));
        throw Provider_Not_Found(algo_name(), provider);
    }

    // decryptor
    std::unique_ptr<PK_Ops::KEM_Decryption>
        Kyber_PrivateKey::create_kem_decryption_op( RandomNumberGenerator& rng,
            const std::string& params,
            const std::string& provider ) const
    {
        BOTAN_UNUSED(rng, params);

        if ( provider == "base" || provider.empty() )
            return std::unique_ptr<PK_Ops::KEM_Decryption>( new Kyber_KEM_Decryptor( *this ) );
        throw Provider_Not_Found( algo_name(), provider );
    }

    bool Kyber_PrivateKey::check_key( RandomNumberGenerator& rng, bool ) const
    {
        auto pub_key_alice = Kyber_PublicKey( this->public_key_bits(), KyberMode::Kyber512 );
        PK_KEM_Encryptor encryptor_bob( pub_key_alice, rng );

        secure_vector<uint8_t> cipher_text, key_bob;
        encryptor_bob.encrypt( cipher_text, key_bob, 32, rng );

        PK_KEM_Decryptor decryptor_bob( *this, rng );
        auto key_alice = decryptor_bob.decrypt( cipher_text.data(), cipher_text.size(), 32 );

        return key_alice == key_bob;
    }
}
