#include <botan/kyber.h>
#include <botan/rng.h>

#include <botan/hash.h>
#include <botan/mem_ops.h>
#include <botan/pubkey.h>
#include <botan/sha3.h>
#include <botan/shake.h>
#include <botan/stream_cipher.h>
#include <botan/loadstor.h>

#include <array>

namespace Botan
{
namespace Internal
{
namespace
{
    constexpr size_t N = 256;
    constexpr size_t Q = 3329;
    constexpr size_t Q_inv = 62209; // q^-1 mod 2^16

    constexpr int16_t zetas[128] = {
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

    constexpr int16_t zetas_inv[128] = {
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
        a -= Q;
        a += (a >> 15) & Q;
        return a;
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
     int16_t montgomery_reduce(int32_t a) {
         int32_t t;
         int16_t u;

         u = a*Q_inv;
         t = (int32_t)u*Q;
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
            const int16_t v = ((1U << 26) + Q/ 2) / Q;

            t = (int32_t)v*a >> 26;
            t *= Q;
            return a - t;
        }

    /*************************************************
    * Name:        prf
    *
    * Description: not 90s: Usage of SHAKE256 as a PRF, concatenates secret and public input
    *              and then generates outlen bytes of SHAKE256 output
    *              90s mode: Usage of AES-256 CRT as a PRF, where "key" is used as the key and "nonce" is zero-padded
    *              to a 12-byte nonce. The counter of CTR mode is initialized to zero
    *
    * Arguments:   - const uint8_t *key: pointer to the key
    *                                    (of length KYBER_SYMBYTES)
    *              - uint8_t nonce:      single-byte nonce (public PRF input)
    * Return:       Output
    **************************************************/
    template <typename Alloc>
    secure_vector<uint8_t> prf(
        const std::vector<uint8_t, Alloc> &seed,
        const uint8_t nonce,
        const KyberMode &mode)
    {
        secure_vector<uint8_t> out;

        if (!mode.is_90s())
        {
            // only normal kyber no 90s
            std::vector<uint8_t> extkey;
            extkey.reserve(seed.size() + 1);
            extkey.insert(extkey.end(), seed.begin(), seed.end());
            extkey.push_back(nonce);

            secure_vector< uint64_t > sponge_state(25);
            size_t sponge_state_pos = Botan::SHA_3::absorb(KyberMode::kShake256Rate, sponge_state, 0, extkey.data(), extkey.size());

            // normal kyber not 90s
            out.resize(mode.eta1() * N / 4);
            Botan::SHA_3::finish(KyberMode::kShake256Rate, sponge_state, sponge_state_pos, 0x1F, 0x80);
            Botan::SHA_3::expand(KyberMode::kShake256Rate, sponge_state, out.data(), out.size());
        }
        else
        {
            throw Botan::Not_Implemented("90s mode is commented out for the time being");

            // 90s mode
            // std::vector<uint8_t> buffer(12, 0);
            // buffer.at(0) = nonce;
            // uint8_t iv[1] = { 0 };

            // std::unique_ptr<Botan::StreamCipher> cipher( Botan::StreamCipher::create( "CTR-BE(AES-256)" ) );
            // cipher->set_key( key, 32 );
            // // IV is zero padded to block length internally
            // cipher->set_iv( iv, 1 );

            // cipher->encrypt( buffer );

            // return {};
        }

        return out;
    }

    class Polynomial {
      public:
        std::array<int16_t, N> coeffs;

        static constexpr size_t kSerializedByteCount = N / 2 * 3;

        /*************************************************
        * Name:        poly_csubq
        *
        * Description: Applies conditional subtraction of q to each coefficient
        *              of a polynomial. For details of conditional subtraction
        *              of q see comments in reduce.c
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void csubq() {
            for (auto& coeff : coeffs) {
                coeff = ::Botan::Internal::csubq(coeff);
            }
        }

        /*************************************************
        * Name:        poly_reduce
        *
        * Description: Applies Barrett reduction to all coefficients of a polynomial
        *              for details of the Barrett reduction see comments in reduce.c
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void reduce()
        {
          for (auto &c : coeffs)
            c = barrett_reduce(c);
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
        template <typename T = std::vector<uint8_t>>
        T tobytes() {
            this->csubq();

            T r(coeffs.size() / 2 * 3);

            for (size_t i = 0; i < coeffs.size() / 2; ++i ) {
                const uint16_t t0 = coeffs[2 * i];
                const uint16_t t1 = coeffs[2 * i + 1];
                r[3 * i + 0] = ( t0 >> 0 );
                r[3 * i + 1] = ( t0 >> 8 ) | ( t1 << 4 );
                r[3 * i + 2] = ( t1 >> 4 );
            }

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
        template <typename Alloc>
        static Polynomial cbd2(const std::vector<uint8_t, Alloc>& buf)
        {
            Polynomial r;

            if (buf.size() < (2 * r.coeffs.size() / 4))
            {
                throw Botan::Invalid_Argument("Cannot cbd2 because buf incompatible buffer length!");
            }


            for (size_t i = 0; i < r.coeffs.size() / 8; ++i) {
                uint32_t t = Botan::load_le<uint32_t>(buf.data(), i);
                uint32_t d = t & 0x55555555;
                d += (t >> 1) & 0x55555555;

                for (size_t j = 0; j < 8; ++j) {
                    int16_t a = (d >> (4 * j + 0)) & 0x3;
                    int16_t b = (d >> (4 * j + 2)) & 0x3;
                    r.coeffs[8 * i + j] = a - b;
                }
            }

            return r;
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
        template <typename Alloc>
        static Polynomial cbd3(const std::vector<uint8_t, Alloc>& buf) // TODO bufLength   uint8_t buf[3 * N / 4]
        {
            Polynomial r;

            if (buf.size() < (3 * r.coeffs.size() / 4))
            {
                throw std::runtime_error("Cannot cbd3 because buf incompatible buffer length!");
            }

            // Note: Botan::load_le<> does not support loading a 3-byte value
            const auto load_le24 = [](const uint8_t in[], const size_t off) {
                const auto off3 = off * 3;
                return Botan::make_uint32(0, in[off3 + 2], in[off3 + 1], in[off3]);
            };

            for (size_t i = 0; i < r.coeffs.size() / 4; ++i) {
                uint32_t t = load_le24(buf.data(), i);
                uint32_t d = t & 0x00249249;
                d += (t >> 1) & 0x00249249;
                d += (t >> 2) & 0x00249249;

                for (size_t j = 0; j < 4; ++j) {
                    int16_t a = (d >> (6 * j + 0)) & 0x7;
                    int16_t b = (d >> (6 * j + 3)) & 0x7;
                    r.coeffs[4 * i + j] = a - b;
                }
            }
            return r;
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
        template <typename Alloc>
        static Polynomial getnoise_eta2(const std::vector<uint8_t, Alloc> &seed, uint8_t nonce, const KyberMode &mode)
        {
            const auto buf = prf(seed, nonce, mode);
            return Polynomial::cbd2(buf);
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
        template <typename Alloc>
        static Polynomial getnoise_eta1(const std::vector<uint8_t, Alloc> &seed, uint8_t nonce, const KyberMode &mode)
        {
            auto buf = prf(seed, nonce, mode);

            if (mode.eta1() == 2)
            {
                return Polynomial::cbd2(buf);
            }
            else if (mode.eta1() == 3)
            {
                return Polynomial::cbd3(buf);
            }

            throw Botan::Invalid_State("unknown ETA1 in kyber getnoise");
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
        template <typename Alloc>
        static Polynomial frombytes( const std::vector<uint8_t, Alloc> &a, const size_t offset=0 ) {
            Polynomial r;
            for ( size_t i = 0; i < r.coeffs.size() / 2; ++i ) {
                r.coeffs[2 * i]     = ( ( a[3 * i + 0 + offset] >> 0 ) | ( (uint16_t)a[3 * i + 1 + offset] << 8 ) ) & 0xFFF;
                r.coeffs[2 * i + 1] = ( ( a[3 * i + 1 + offset] >> 4 ) | ( (uint16_t)a[3 * i + 2 + offset] << 4 ) ) & 0xFFF;
            }
            return r;
        }

        /*************************************************
        * Name:        poly_frommsg
        *
        * Description: Convert 32-byte message to polynomial
        *
        * Arguments:   - poly *r:            pointer to output polynomial
        *              - const uint8_t *msg: pointer to input message
        **************************************************/
        template <typename Alloc>
        static Polynomial from_message( const std::vector<uint8_t, Alloc> &msg)
        {
            Polynomial r;
            if (msg.size() != N / 8)
            {
                throw Botan::Invalid_Argument("KYBER_INDCPA_MSGBYTES must be equal to KYBER_N/8 bytes! (is " + std::to_string(msg.size()) + ")");
            }

            for (size_t i = 0;i<r.coeffs.size() / 8;++i) {
                for (size_t j = 0;j<8;j++) {
                    const auto mask = -(int16_t)((msg[i] >> j) & 1);
                    r.coeffs[8 * i + j] = mask & ((Q + 1) / 2);
                }
            }
            return r;
        }

        /*************************************************
        * Name:        poly_tomsg
        *
        * Description: Convert polynomial to 32-byte message
        *
        * Arguments:   - uint8_t *msg: pointer to output message
        *              - poly *a:      pointer to input polynomial
        **************************************************/
        void tomsg(uint8_t msg[32]) {  // TODO msg [ symbytes]
            this->csubq();

            for (size_t i = 0;i<coeffs.size() / 8;++i) {
                msg[i] = 0;
                for (size_t j = 0;j<8;++j) {
                    uint16_t t = ((((uint16_t)this->coeffs[8 * i + j] << 1) + Q / 2) / Q) & 1;
                    msg[i] |= t << j;
                }
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
        Botan::secure_vector<uint8_t> compress(const size_t k)
        {
            BOTAN_ASSERT(k == 2 || k == 3 || k == 4, "k should be one of {2,3,4}");

            const size_t compressed_bytes = (k == 2 || k == 3) ? 128 : 160;
            Botan::secure_vector<uint8_t> r(compressed_bytes);

            csubq();

            uint8_t t[8];
            if( k == 2 || k == 3 )
            {
                size_t offset = 0;
                for ( size_t i = 0; i < coeffs.size() / 8; ++i ) {
                    for ( size_t j = 0; j < 8; ++j )
                        t[j] = ( ( ( (uint16_t)coeffs[8 * i + j] << 4 ) + Q / 2 ) / Q) & 15;

                    r[0 + offset] = t[0] | ( t[1] << 4 );
                    r[1 + offset] = t[2] | ( t[3] << 4 );
                    r[2 + offset] = t[4] | ( t[5] << 4 );
                    r[3 + offset] = t[6] | ( t[7] << 4 );
                    offset += 4;
                }
            }
            else if( k == 4 )
            {
                size_t offset = 0;
                for ( size_t i = 0; i < coeffs.size() / 8; ++i ) {
                    for ( size_t j = 0; j < 8; ++j )
                        t[j] = ( ( ( (uint32_t)coeffs[8 * i + j] << 5 ) + Q / 2 ) / Q) & 31;

                    r[0 + offset] = ( t[0] >> 0 ) | ( t[1] << 5 );
                    r[1 + offset] = ( t[1] >> 3 ) | ( t[2] << 2 ) | ( t[3] << 7 );
                    r[2 + offset] = ( t[3] >> 1 ) | ( t[4] << 4 );
                    r[3 + offset] = ( t[4] >> 4 ) | ( t[5] << 1 ) | ( t[6] << 6 );
                    r[4 + offset] = ( t[6] >> 2 ) | ( t[7] << 3 );
                    offset += 5;
                }
            }

            return r;
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
        Polynomial& operator +=(const Polynomial& other) {
            for (size_t i = 0;i<this->coeffs.size();++i)
                this->coeffs[i] = this->coeffs[i] + other.coeffs[i];
            return *this;
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
        Polynomial& operator -=(const Polynomial& other) {
            for (size_t i = 0;i<this->coeffs.size();++i)
                this->coeffs[i] = other.coeffs[i] - this->coeffs[i];
            return *this;
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
        static Polynomial basemul_montgomery(const Polynomial &a, const Polynomial &b)
        {
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
            auto basemul = [](int16_t r[2],
                              const int16_t a[2],
                              const int16_t b[2],
                              const int16_t zeta)
            {
                r[0] = fqmul(a[1], b[1]);
                r[0] = fqmul(r[0], zeta);
                r[0] += fqmul(a[0], b[0]);

                r[1] = fqmul(a[0], b[1]);
                r[1] += fqmul(a[1], b[0]);
            };

            Polynomial r;

            for (size_t i = 0; i<r.coeffs.size() / 4; ++i) {
                basemul(&r.coeffs[4 * i], &a.coeffs[4 * i], &b.coeffs[4 * i], zetas[64 + i]);
                basemul(&r.coeffs[4 * i + 2], &a.coeffs[4 * i + 2], &b.coeffs[4 * i + 2],
                    -zetas[64 + i]);
            }

            return r;
        }

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
        static Polynomial sample_rej_uniform(size_t &out_count, std::vector<uint8_t> buf)
        {
            Polynomial p;
            out_count = 0;

            size_t pos = 0;
            while (out_count < p.coeffs.size() && pos + 3 <= buf.size()) {
                size_t val0 = ((buf[pos + 0] >> 0) | ((uint16_t)buf[pos + 1] << 8)) & 0xFFF;
                size_t val1 = ((buf[pos + 1] >> 4) | ((uint16_t)buf[pos + 2] << 4)) & 0xFFF;
                pos += 3;

                if (val0 < Q)
                    p.coeffs[out_count++] = val0;
                if (out_count < p.coeffs.size() && val1 < Q)
                    p.coeffs[out_count++] = val1;
            }

            return p;
        }

        /*************************************************
        * Name:        poly_tomont
        *
        * Description: Inplace conversion of all coefficients of a polynomial
        *              from normal domain to Montgomery domain
        *
        * Arguments:   - poly *r: pointer to input/output polynomial
        **************************************************/
        void tomont() {
            const int16_t f = (1ULL << 32) % Q;
            for (auto &c : coeffs)
              c = montgomery_reduce((int32_t)c * f);
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
        void ntt()
        {
            for (size_t len = coeffs.size()/2, k = 0; len >= 2; len /= 2) {
                for (size_t start = 0, j = 0; start < coeffs.size(); start = j + len) {
                    const auto zeta = zetas[++k];
                    for (j = start; j < start + len; ++j) {
                        const auto t = fqmul(zeta, coeffs[j + len]);
                        coeffs[j + len] = coeffs[j] - t;
                        coeffs[j] = coeffs[j] + t;
                    }
                }
            }

            reduce();
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
        void invntt_tomont()
        {
            for (size_t len = 2, k = 0; len <= coeffs.size()/2; len *= 2) {
                for (size_t start = 0, j = 0; start < coeffs.size(); start = j + len) {
                    const auto zeta = zetas_inv[k++];
                    for (j = start; j < start + len; ++j) {
                        const auto t = coeffs[j];
                        coeffs[j] = barrett_reduce(t + coeffs[j + len]);
                        coeffs[j + len] = fqmul(zeta, t - coeffs[j + len]);
                    }
                }
            }

            for (auto &c : coeffs)
                c = fqmul(c, zetas_inv[127]);
        }
    };


    class PolynomialVector
    {
    public:
        PolynomialVector() = delete;
        explicit PolynomialVector(const size_t k)
            : vec(k) {}

        std::vector<Polynomial> vec;

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
        template <typename Alloc>
        static PolynomialVector frombytes( const std::vector<uint8_t, Alloc> &a, const size_t k /* TODO: calculate that? */ )
        {
            BOTAN_ASSERT(a.size() >= Polynomial::kSerializedByteCount * k, "wrong byte length for frombytes");

            PolynomialVector r(k);
            for (size_t i = 0; i < k; ++i)
                r.vec[i] = Polynomial::frombytes( a, i * Polynomial::kSerializedByteCount );
            return r;
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
        static Polynomial pointwise_acc_montgomery(
            const PolynomialVector &a,
            const PolynomialVector &b)
        {
            BOTAN_ASSERT(a.vec.size() == b.vec.size(),
                         "pointwise_acc_montgomery works on equally sized PolynomialVectors only");

            auto r = Polynomial::basemul_montgomery(a.vec[0], b.vec[0]);
            for (size_t i = 1; i < a.vec.size(); ++i) {
                r += Polynomial::basemul_montgomery(a.vec[i], b.vec[i]);
            }

            r.reduce();
            return r;
        }

        template <typename Alloc>
        static PolynomialVector getnoise_eta2(const std::vector<uint8_t, Alloc> &seed, uint8_t nonce, const KyberMode &mode)
        {
            PolynomialVector r(mode.k());

            for (auto& p : r.vec)
            {
                p = Polynomial::getnoise_eta2(seed, nonce++, mode);
            }

            return r;
        }

        template <typename Alloc>
        static PolynomialVector getnoise_eta1(const std::vector<uint8_t, Alloc> &seed, uint8_t nonce, const KyberMode &mode)
        {
            PolynomialVector r(mode.k());

            for (auto& p : r.vec)
            {
                p = Polynomial::getnoise_eta1(seed, nonce++, mode);
            }

            return r;
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
        template <typename T = std::vector<uint8_t>>
        T tobytes(const size_t k)
        {
            T r;

            r.reserve(k * Polynomial::kSerializedByteCount);
            for ( size_t i = 0; i < k; ++i ) // TODO: use foreach
            {
                const auto poly = vec[i].tobytes<T>();
                r.insert(r.end(), poly.begin(), poly.end());
            }

            return r;
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
        Botan::secure_vector<uint8_t> compress()
        {
            const auto k = vec.size();
            BOTAN_ASSERT(k == 2 || k == 3 || k == 4, "k should be one of {2,3,4}");

            const size_t compressed_bytes = (k == 2 || k == 3) ? k * 320 : k * 352;
            Botan::secure_vector<uint8_t> r(compressed_bytes);

            csubq();

            if ( k == 2 || k == 3 )
            {
                uint16_t t[4];
                size_t offset = 0;
                for ( size_t i = 0; i < k; ++i ) {
                    for ( size_t j = 0; j < N / 4; ++j ) {
                        for ( size_t kk = 0; kk < 4; ++kk )
                            t[kk] = ( ( ( (uint32_t)vec[i].coeffs[4 * j + kk] << 10 ) + Q / 2 )
                                / Q ) & 0x3ff;

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
                uint16_t t[8];
                size_t offset = 0;
                for ( size_t i = 0; i < k; ++i ) {
                    for ( size_t j = 0; j < N / 8; ++j ) {
                        for ( size_t kk = 0; kk < 8; ++kk )
                            t[kk] = ( ( ( (uint32_t)vec[i].coeffs[8 * j + kk] << 11 ) + Q / 2 )
                                / Q ) & 0x7ff;

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

            return r;
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
        void csubq()
        {
          for (auto& p : vec) {
                p.csubq();
          }
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
        PolynomialVector& operator+=(const PolynomialVector &other)
        {
            for (size_t i = 0; i<vec.size(); ++i)
                vec[i] += other.vec[i];
            return *this;
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
        void reduce()
        {
            for (auto &v : vec)
                v.reduce();
        }

        /*************************************************
        * Name:        polyvec_invntt_tomont
        *
        * Description: Apply inverse NTT to all elements of a vector of polynomials
        *              and multiply by Montgomery factor 2^16
        *
        * Arguments:   - polyvec *r: pointer to in/output vector of polynomials
        **************************************************/
        void invntt_tomont()
        {
            for (auto &v : vec)
                v.invntt_tomont();
        }

        /*************************************************
        * Name:        polyvec_ntt
        *
        * Description: Apply forward NTT to all elements of a vector of polynomials
        *
        * Arguments:   - polyvec *r: pointer to in/output vector of polynomials
        **************************************************/
        void ntt()
        {
            for (auto &v : vec)
                v.ntt();
        }
    };

    class PolynomialMatrix
    {
    public:
        PolynomialMatrix() = delete;

        std::vector<PolynomialVector> mat;

        static PolynomialMatrix generate(const std::vector<uint8_t>& seed, const bool transposed, const KyberMode &mode)
        {
            return (mode.is_90s()) ? generate_90s(seed, transposed, mode)
                                   : generate_normal(seed, transposed, mode);
        }

        PolynomialVector pointwise_acc_montgomery(const PolynomialVector &vec, const bool with_mont = false)
        {
            PolynomialVector result(mat.size());

            for (size_t i = 0; i < mat.size(); ++i)
            {
                result.vec[i] = PolynomialVector::pointwise_acc_montgomery(mat[i], vec);
                if (with_mont)
                {
                    result.vec[i].tomont();
                }
            }

            return result;
        }


    private:
        explicit PolynomialMatrix(const KyberMode &mode)
            : mat(mode.k(), PolynomialVector(mode.k())) {}

        // normal mode, not 90s
        // We instantiate XOF with SHAKE-128
        static PolynomialMatrix generate_normal(const std::vector<uint8_t>& seed, const bool transposed, const KyberMode &mode)
        {
            BOTAN_ASSERT(seed.size() == KyberMode::kSymBytes, "unexpected seed size");

            PolynomialMatrix matrix(mode);

            for ( size_t i = 0; i < mode.k(); ++i ) {
                for ( size_t j = 0; j < mode.k(); ++j ) {
                    secure_vector< uint64_t > sponge_state(25);

                    secure_vector<uint8_t> extseed1;
                    extseed1.reserve(seed.size() + 2);
                    extseed1.insert(extseed1.end(), seed.cbegin(), seed.cend());

                    if (transposed)
                    {
                      extseed1.push_back(i);
                      extseed1.push_back(j);
                    }
                    else
                    {
                      extseed1.push_back(j);
                      extseed1.push_back(i);
                    }

                    size_t sponge_state_pos = Botan::SHA_3::absorb( KyberMode::kShake128Rate, sponge_state, 0, extseed1.data(), extseed1.size() );

                    const size_t matrix_length = 12 * N / 8 * (1 << 12) / Q + mode.xof_block_bytes();

                    // 2 extra bytes to buf_std for the expansion in the while loop  --  or not??
                    std::vector <uint8_t> buf(matrix_length); // + 2 );
                    Botan::SHA_3::finish( KyberMode::kShake128Rate, sponge_state, sponge_state_pos, 0x1F, 0x80 );
                    Botan::SHA_3::expand( KyberMode::kShake128Rate, sponge_state, buf.data(), matrix_length );

                    size_t unused;
                    matrix.mat[i].vec[j] = Polynomial::sample_rej_uniform(unused, buf);

    //                  TODO: This while loop is never run and all tests are passing without it.
    //                        It seems it would be called if rej_uniform exits via the second condition -- `pos + 3 <= buflen`. But I don't know
    //                        if this is something that can happen. Can this be removed?
    //
    //                     ctr = rej_uniform( a[i].vec[j].coeffs.data(), N, buf_std.data(), matrix_length );
    //                     while ( ctr < N ) {
    //                         const size_t off = matrix_length % 3;
    //                         for ( k = 0; k < off; k++ )
    //                             buf_std[k] = buf_std[matrix_length - off + k];

    //                         Botan::SHA_3::permute( spongeState.data() );
    //                         Botan::SHA_3::expand( KyberMode::kShake128Rate, spongeState, buf_std.data() + off, 168 );

    //                         matrix_length = off + mode.xof_block_bytes();
    //                         std::cout << "mat len now: " << matrix_length << std::endl;
    //                         ctr += rej_uniform( a[i].vec[j].coeffs.data() + ctr, N - ctr, buf_std.data(), matrix_length );
    //                     }
                }
            }

            return matrix;
        }

        // 90s mode
        // We instantiate XOF(seed, i, j) with AES-256 in CTR mode, where seed is used as the key and i||j is zeropadded
        // to a 12 - byte nonce. The counter of CTR mode is initialized to zero.
        static PolynomialMatrix generate_90s(const std::vector<uint8_t>& seed, const bool transposed, const KyberMode &mode)
        {
          BOTAN_UNUSED(seed, transposed, mode);
          throw Botan::Not_Implemented("90s is commented for now");
            //std::vector<PolynomialVector> a(m_k, PolynomialVector(m_k));

            //unsigned int ctr, i, j, k;
            //unsigned int buflen, off;

            //for ( i = 0; i < m_k; i++ ) {
            //    for ( j = 0; j < m_k; j++ ) {
            //        std::vector<uint8_t> buffer( 12, 0 );
            //        if ( transposed )
            //        {
            //            buffer.at( 0 ) = i;
            //            buffer.at( 1 ) = j;
            //        }
            //        else
            //        {
            //            buffer.at( 0 ) = j;
            //            buffer.at( 1 ) = i;
            //        }

            //        // absorb
            //        std::unique_ptr<Botan::StreamCipher> cipher( Botan::StreamCipher::create( "CTR-BE(AES-256)" ) );
            //        cipher->set_key( seed );
            //        // IV is zero padded to block length internally
            //        uint8_t iv[1] = { 0 };
            //        cipher->set_iv( iv, 1 );

            //        // is this still squeeze or already the first absorb?
            //        cipher->encrypt( buffer );

            //        buflen = m_gen_matrix_nblocks * m_XOF_BLOCKBYTES;
            //        // 2 extra bytes to buf_std for the expansion in the while loop
            //        std::vector <uint8_t> buf_std( buflen + 2 );
            //        //Botan::SHA_3::finish( m_SHAKE128_RATE, spongeState, spongeStatePos, 0x1F, 0x80 );
            //        //Botan::SHA_3::expand( m_SHAKE128_RATE, spongeState, buf_std.data(), buflen );

            //        ctr = rej_uniform( a[i].vec[j].coeffs.data(), m_N, buf_std.data(), buflen );

            //        while ( ctr < m_N ) {
            //            off = buflen % 3;
            //            for ( k = 0; k < off; k++ )
            //                buf_std[k] = buf_std[buflen - off + k];


            //            // normal kyber not 90s
            //           // Botan::SHA_3::permute( spongeState.data() );
            //            //Botan::SHA_3::expand( m_SHAKE128_RATE, spongeState, buf_std.data() + off, 168 );


            //            buflen = off + m_XOF_BLOCKBYTES;
            //            ctr += rej_uniform( a[i].vec[j].coeffs.data() + ctr, m_N - ctr, buf_std.data(), buflen );
            //        }
            //    }
            //}

            //return a;
        }
    };

    }  // anonymous namespace
    }  // namespace Internal

    class Kyber_PublicKeyInternal {
    public:
        Kyber_PublicKeyInternal(KyberMode mode, std::vector<uint8_t> polynomials, std::vector<uint8_t> seed)
            : m_mode(std::move(mode))
            , m_polynomials(Internal::PolynomialVector::frombytes(std::move(polynomials), mode.k()))
            , m_seed(std::move(seed)) {}

        Kyber_PublicKeyInternal(KyberMode mode, Internal::PolynomialVector polynomials, std::vector<uint8_t> seed)
            : m_mode(std::move(mode))
            , m_polynomials(std::move(polynomials))
            , m_seed(std::move(seed)) {}

        Internal::PolynomialVector& polynomials() { return m_polynomials; }
        const std::vector<uint8_t>& seed() const { return m_seed; }
        const KyberMode& mode() const { return m_mode; }

        Kyber_PublicKeyInternal() = delete;

    private:
        KyberMode                  m_mode;
        Internal::PolynomialVector m_polynomials;
        std::vector<uint8_t>       m_seed;
    };

    class Kyber_PrivateKeyInternal {
    public:
        Kyber_PrivateKeyInternal(Internal::PolynomialVector polynomials, std::vector<uint8_t> pubkey_hash, secure_vector<uint8_t> z)
            : m_polynomials(std::move(polynomials))
            , m_public_key_hash(std::move(pubkey_hash))
            , m_z(std::move(z)) {}

        Internal::PolynomialVector& polynomials() { return m_polynomials; }
        const std::vector<uint8_t>& public_key_hash() const { return m_public_key_hash; }
        const secure_vector<uint8_t>& z() const { return m_z; }

        Kyber_PrivateKeyInternal() = delete;

    private:
        Internal::PolynomialVector m_polynomials;
        std::vector<uint8_t>       m_public_key_hash;
        secure_vector<uint8_t>     m_z;
    };

    namespace Internal {
    namespace {

    class Internal_Operation final
    {
    public:


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
        PolynomialVector polyvec_decompress( const uint8_t* a, size_t a_len )
        {
            PolynomialVector r(m_k);
            unsigned int i, j, k;

            if( a_len == m_k * 352 + m_poly_compressed_bytes )
            {
                uint16_t t[8];
                for ( i = 0; i < m_k; i++ ) {
                    for ( j = 0; j < N / 8; j++ ) {
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
                            r.vec[i].coeffs[8 * j + k] = ( (uint32_t)( t[k] & 0x7FF ) * Q + 1024 ) >> 11;
                    }
                }

                return r;
            }
            else if( a_len == m_k * 320 + m_poly_compressed_bytes )
            {
                uint16_t t[4];
                for ( i = 0; i < m_k; i++ ) {
                    for ( j = 0; j < N / 4; j++ ) {
                        t[0] = ( a[0] >> 0 ) | ( (uint16_t)a[1] << 8 );
                        t[1] = ( a[1] >> 2 ) | ( (uint16_t)a[2] << 6 );
                        t[2] = ( a[2] >> 4 ) | ( (uint16_t)a[3] << 4 );
                        t[3] = ( a[3] >> 6 ) | ( (uint16_t)a[4] << 2 );
                        a += 5;

                        for ( k = 0; k < 4; k++ )
                            r.vec[i].coeffs[4 * j + k] = ( (uint32_t)( t[k] & 0x3FF ) * Q + 512 ) >> 10;
                    }
                }

                return r;
            }
            else
            {
                throw std::runtime_error( "KYBER_POLYVECCOMPRESSEDBYTES needs to be in {320*KYBER_K, 352*KYBER_K}" );
            }
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
        PolynomialVector unpack_sk( const std::vector<uint8_t> packedsk )
        {
            return PolynomialVector::frombytes( packedsk, m_k );
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
        PolynomialVector unpack_pk( std::vector<uint8_t>& seed, const std::vector<uint8_t>& packedpk )
        {
            auto pk = PolynomialVector::frombytes( packedpk, m_k );
            for ( size_t i = 0; i < get_sym_bytes(); ++i )
                seed[i] = packedpk[i + get_poly_vec_bytes()];
            return pk;
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
        void poly_decompress(Polynomial *r, const uint8_t a[], size_t aLength ) // TODO a[KYBER_POLYCOMPRESSEDBYTES]
        {
            unsigned int i;

            if (aLength == 128)
            {
                for (i = 0;i < N / 2;i++) {
                    r->coeffs[2 * i + 0] = (((uint16_t)(a[0] & 15)*Q) + 8) >> 4;
                    r->coeffs[2 * i + 1] = (((uint16_t)(a[0] >> 4)*Q) + 8) >> 4;
                    a += 1;
                }
            }
            else if(aLength == 160)
            {
                unsigned int j;
                uint8_t t[8];
                for (i = 0;i < N / 8;i++) {
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
                        r->coeffs[8 * i + j] = ((uint32_t)(t[j] & 31)*Q + 16) >> 5;
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
        PolynomialVector unpack_ciphertext( Polynomial* v, const uint8_t* c, size_t c_len )
        {
            auto b = polyvec_decompress( c, c_len );
            poly_decompress( v, c + m_poly_vec_compressed_bytes, m_poly_compressed_bytes);

            return b;
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
            Polynomial v;

            auto bp = unpack_ciphertext( &v, c, c_len );
            auto skpv = unpack_sk( sk );

            bp.ntt();
            auto mp = PolynomialVector::pointwise_acc_montgomery(skpv, bp);
            mp.invntt_tomont();

            mp -= v;
            mp.reduce();
            mp.tomsg(m);
        }

        Internal_Operation( KyberMode mode ) : m_mode(mode)
        {
            switch ( mode.mode )
            {
            case KyberMode::Kyber512:
            case KyberMode::Kyber512_90s:
                m_k = 2;
                m_poly_vec_compressed_bytes = m_k * 320;
                m_poly_compressed_bytes = 128;
                m_KYBER_ETA1 = 3;
                break;
            case KyberMode::Kyber768:
            case KyberMode::Kyber768_90s:
                m_k = 3;
                m_poly_vec_compressed_bytes = m_k * 320;
                m_poly_compressed_bytes = 128;
                m_KYBER_ETA1 = 2;
                break;
            case KyberMode::Kyber1024:
            case KyberMode::Kyber1024_90s:
                m_k = 4;
                m_poly_vec_compressed_bytes = m_k * 352;
                m_poly_compressed_bytes = 160;
                m_KYBER_ETA1 = 2;
                break;
            default:
                throw std::runtime_error( "invalid kyber mode" );
                break;
            }
            if( mode.mode == KyberMode::Kyber512_90s || mode.mode == KyberMode::Kyber768_90s || mode.mode == KyberMode::Kyber1024_90s )
            {
                m_kyber_90s = true;
                m_XOF_BLOCKBYTES = m_XOF_BLOCKBYTES_90s;
            }
            else
            {
                m_kyber_90s = false;
                m_XOF_BLOCKBYTES = m_XOF_BLOCKBYTES_non_90s;
            }


            m_poly_vec_bytes = m_k * m_poly_bytes;
            m_public_key_bytes = m_poly_vec_bytes + m_sym_bytes;
            m_secret_key_bytes = m_poly_vec_bytes + m_public_key_bytes + 2 * m_sym_bytes;
            m_ciphertext_bytes = m_poly_vec_compressed_bytes + m_poly_compressed_bytes;
        }

        size_t get_public_key_bytes() const { return m_public_key_bytes; }
        size_t get_poly_vec_bytes() const { return m_poly_vec_bytes; }
        size_t get_poly_bytes() const { return m_poly_bytes; }
        size_t get_secret_key_bytes() const { return m_secret_key_bytes; }
        size_t get_sym_bytes() const { return m_sym_bytes; }
        size_t get_ciphertext_bytes() const { return m_ciphertext_bytes; }
        size_t is_90s() const { return m_kyber_90s; }



        constexpr static size_t m_sym_bytes = 32;
        // constexpr static size_t m_ss_bytes = 32;

        constexpr static size_t m_poly_bytes = 384;

        // constexpr static size_t m_ETA2 = 2;
        constexpr static size_t m_XOF_BLOCKBYTES_non_90s  = 168; // SHAKE128 Rate
        constexpr static size_t m_XOF_BLOCKBYTES_90s = 64; // AES256CTR_BLOCKBYTES

        size_t m_k;
        size_t m_poly_vec_bytes;
        size_t m_poly_vec_compressed_bytes;
        size_t m_poly_compressed_bytes;
        size_t m_public_key_bytes;
        size_t m_secret_key_bytes;
        size_t m_ciphertext_bytes;
        size_t m_XOF_BLOCKBYTES;
        size_t m_KYBER_ETA1;
        bool m_kyber_90s;

        KyberMode m_mode;
    };

}
}
}

namespace Botan
{
    namespace {

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
    secure_vector<uint8_t> pack_ciphertext(Internal::PolynomialVector &b, Internal::Polynomial &v, const KyberMode &mode)
    {
        auto ct = b.compress();
        const auto p = v.compress(mode.k());
        ct.insert(ct.end(), p.begin(), p.end());

        return ct;
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
    secure_vector<uint8_t> indcpa_enc(
        const Botan::secure_vector<uint8_t>            &m,
        const Botan::secure_vector<uint8_t>            &coins,
        const std::shared_ptr<Kyber_PublicKeyInternal>  pk,
        const KyberMode                                &mode)
    {
        auto sp  = Internal::PolynomialVector::getnoise_eta1(coins, 0, mode);
        auto ep  = Internal::PolynomialVector::getnoise_eta2(coins, mode.k(), mode);
        auto epp = Internal::Polynomial::getnoise_eta2(coins, 2 * mode.k(), mode);

        auto k = Internal::Polynomial::from_message(m);
        auto at = Internal::PolynomialMatrix::generate(pk->seed(), true, mode);

        sp.ntt();

        // matrix-vector multiplication
        auto bp = at.pointwise_acc_montgomery(sp);
        auto v = Internal::PolynomialVector::pointwise_acc_montgomery(pk->polynomials(), sp );

        bp.invntt_tomont();
        v.invntt_tomont();

        bp += ep;
        v += epp;
        v += k;
        bp.reduce();
        v.reduce();

        return pack_ciphertext(bp, v, mode);
    }
    }



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
            secure_vector<uint8_t> ciphertext = kyber_encrypt(plaintext, rng);

            out_shared_key.swap(plaintext);
            out_encapsulated_key.swap(ciphertext);
        }

    private:

        secure_vector<uint8_t> kyber_encrypt(
            secure_vector<uint8_t>& sharedSecret, RandomNumberGenerator& rng)
        {
            const auto sym_bytes = KyberMode::kSymBytes;
            secure_vector<uint8_t> buf( sym_bytes );
            rng.randomize( buf.data(), buf.size() );
            /* Don't release system RNG output */

            // naming from kyber spec
            std::unique_ptr<HashFunction> H;
            std::unique_ptr<HashFunction> G;
            std::unique_ptr<HashFunction> KDF( HashFunction::create( "SHAKE-256" ) );
            if( !m_key.get_mode().is_90s() )
            {
                H = HashFunction::create( "SHA-3(256)" );
                G = HashFunction::create( "SHA-3(512)" );
            }
            else
            {
                H = HashFunction::create( "SHA-256" );
                G = HashFunction::create( "SHA-512" );
            }


            secure_vector<uint8_t> secBuf;
            secure_vector<uint8_t> secKr;

            H->update(buf);
            secBuf = H->final();

            // Multitarget countermeasure for coins + contributory KEM
            H->update(m_key.public_key_bits());
            auto tmp = H->final();

            G->update(secBuf);
            G->update(tmp);
            secKr = G->final();


            // coins are in kr+KYBER_SYMBYTES
            auto ct = indcpa_enc(secBuf, {secKr.begin() + sym_bytes, secKr.end()}, m_key.m_public, m_key.get_mode());

            // overwrite coins in kr with H(c)
            H->update(ct);
            tmp = H->final();

            std::copy(tmp.begin(), tmp.end(), secKr.begin() + sym_bytes);

            // hash concatenation of pre-k and H(c) to k
            KDF->update(secKr.data(), 2 * sym_bytes );
            sharedSecret = KDF->final();

            return ct;
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
            Botan::Internal::Internal_Operation Internal( m_key.get_mode() );
            const std::vector<uint8_t> pk( sk_unlocked.begin() + Internal.get_poly_vec_bytes(), sk_unlocked.end() );

            // naming from kyber spec
            std::unique_ptr<HashFunction> H;
            std::unique_ptr<HashFunction> G;
            std::unique_ptr<HashFunction> KDF( HashFunction::create( "SHAKE-256" ) );
            if ( !Internal.is_90s() )
            {
                H = HashFunction::create( "SHA-3(256)" );
                G = HashFunction::create( "SHA-3(512)" );
            }
            else
            {
                H = HashFunction::create( "SHA-256" );
                G = HashFunction::create( "SHA-512" );
            }

            secure_vector<uint8_t> secBuf;
            secure_vector<uint8_t> secKr;

            Internal.indcpa_dec(buf, ct, ct_len, sk_unlocked );
            // Use secBuf. Insert data from buf
            const auto sym_bytes = Internal.get_sym_bytes();
            secBuf.insert(secBuf.begin(), buf, buf + 2 * sym_bytes);

            /* Multitarget countermeasure for coins + contributory KEM */
            const auto secret_key_bytes = Internal.get_secret_key_bytes();
            for (i = 0; i < sym_bytes; i++)
            {
                secBuf.at(sym_bytes + i) = sk_unlocked.at( secret_key_bytes - 2 * sym_bytes + i);
            }
            G->update(secBuf);
            secKr = G->final();



            /* coins are in kr+KYBER_SYMBYTES */
            auto cmp = indcpa_enc({secBuf.begin(), secBuf.begin() + sym_bytes}, {secKr.begin() + sym_bytes, secKr.end()}, m_key.m_public, m_key.get_mode());

            const auto ciphertext_bytes = Internal.get_ciphertext_bytes();
            fail = !constant_time_compare(ct, cmp.data(), ciphertext_bytes);

            /* overwrite coins in kr with H(c) */
            H->update(ct, ciphertext_bytes );
            auto tmp = H->final();
            secure_vector<uint8_t> secKrFinal{ secKr.begin(), secKr.begin() + sym_bytes };
            secKrFinal.insert(secKrFinal.end(),tmp.begin(),tmp.end());

            secure_vector<uint8_t> secKrFinalFail( sk_data + secret_key_bytes - sym_bytes, sk_data + secret_key_bytes);
            /* hash concatenation of pre-k and H(c) to k */
            /* Overwrite pre-k with z on re-encryption failure */
            fail ? H->update(secKrFinalFail) : KDF->update(secKrFinal);
            ss = KDF->final();
        }

        const Kyber_PrivateKey& m_key;
    };


    KyberMode::KyberMode(const Mode mode)
        : mode(mode)
    {
        m_90s = true;
        m_xof_block_bytes = 64; // AES-256 block size

        switch (mode)
        {
        case KyberMode::Kyber512:
            m_90s = false;
            m_xof_block_bytes = 168; // SHAKE128 rate
            // fall through
        case KyberMode::Kyber512_90s:
            m_nist_strength = 128; // NIST Strength 1 - AES-128
            m_k = 2;
            m_eta1 = 3;
            break;

        case KyberMode::Kyber768:
            m_90s = false;
            m_xof_block_bytes = 168; // SHAKE128 rate
            // fall through
        case KyberMode::Kyber768_90s:
            m_nist_strength = 192; // NIST Strength 3 - AES-192
            m_k = 3;
            m_eta1 = 2;
            break;

        case KyberMode::Kyber1024:
            m_90s = false;
            m_xof_block_bytes = 168; // SHAKE128 rate
            // fall through
        case KyberMode::Kyber1024_90s:
            m_nist_strength = 256; // NIST Strength 5 - AES-256
            m_k = 4;
            m_eta1 = 2;
            break;

        default:
            throw Botan::Invalid_State(std::string("unexpected kyber mode: ") + std::to_string(mode));
        }
    }

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
        return m_mode.estimated_strength();
    }

    Kyber_PublicKey::Kyber_PublicKey( const std::vector<uint8_t>& pub_key, KyberMode mode )
        : m_mode(mode)
        {
            if (pub_key.size() != key_length()) {
                throw Botan::Invalid_Argument("kyber public key does not have the correct byte count");
            }

            std::vector<uint8_t> poly_vec(pub_key.begin(), pub_key.end() - KyberMode::kSeedLength);
            std::vector<uint8_t> seed(pub_key.end() - KyberMode::kSeedLength, pub_key.end());

            m_public = std::make_shared<Kyber_PublicKeyInternal>(std::move(mode), std::move(poly_vec), std::move(seed));
        }

    std::vector<uint8_t> Kyber_PublicKey::public_key_bits() const
    {
        auto pub_key = m_public->polynomials().tobytes<std::vector<uint8_t>>(k());
        pub_key.insert(pub_key.end(), m_public->seed().begin(), m_public->seed().end());
        return pub_key;
    }

    size_t Kyber_PublicKey::key_length() const { return Internal::Polynomial::kSerializedByteCount * k() + KyberMode::kSeedLength; }
    KyberMode Kyber_PublicKey::get_mode() const { return m_public->mode(); }
    size_t Kyber_PublicKey::k() const {
        return m_mode.k();
    }

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
        : Kyber_PublicKey(mode)
    {
        Botan::Internal::Internal_Operation kyberIntOps( mode );

        // TODO: do we actually need to hash the random output?
        constexpr static auto rand_size = 32;
        byte rand[rand_size];
        rng.randomize( rand, rand_size );
        std::unique_ptr<HashFunction> hash3( HashFunction::create( "SHA-3(512)" ) );
        hash3->update( rand, rand_size );
        auto seed0 = hash3->final();

        std::vector<uint8_t>   seed1(seed0.begin(),      seed0.begin() + 32);
        secure_vector<uint8_t> seed2(seed0.begin() + 32, seed0.begin() + 64);

        auto a    = Internal::PolynomialMatrix::generate(seed1, false, mode);
        auto skpv = Internal::PolynomialVector::getnoise_eta1(seed2, 0, mode);
        auto e    = Internal::PolynomialVector::getnoise_eta1(seed2, mode.k(), mode);

        skpv.ntt();
        e.ntt();

        // matrix-vector multiplication
        auto pkpv = a.pointwise_acc_montgomery(skpv, true);
        pkpv += e;
        pkpv.reduce();

        m_public = std::make_shared<Kyber_PublicKeyInternal>(mode, std::move(pkpv), std::move(seed1));

        auto sk = skpv.tobytes<secure_vector<uint8_t>>(mode.k());
        auto pk = public_key_bits();

        std::unique_ptr<HashFunction> hash4(HashFunction::create("SHA-3(256)"));
        hash4->update(pk);
        auto pk_hash = hash4->final_stdvec();

        /* Value z for pseudo-random output on reject */
        auto z = rng.random_vec(kyberIntOps.get_sym_bytes());

        m_private = std::make_shared<Kyber_PrivateKeyInternal>(std::move(skpv), std::move(pk_hash), std::move(z));
    }

    Kyber_PrivateKey::Kyber_PrivateKey( secure_vector<uint8_t> sk, std::vector<uint8_t> pk, KyberMode mode )
        : Kyber_PublicKey(pk, std::move(mode))
    {
        // TODO: test me

        const auto skpv_length    = Internal::Polynomial::kSerializedByteCount * k();
        const auto pk_length      = Internal::Polynomial::kSerializedByteCount * k() + KyberMode::kSeedLength;
        const auto pk_hash_length = 32;
        const auto z_length       = 32;
        const auto private_key_length = skpv_length + pk_length + pk_hash_length + z_length;

        if (private_key_length != sk.size()) {
            throw Botan::Invalid_Argument("kyber private key does not have the correct byte count");
        }

        const secure_vector<uint8_t> skpv(sk.begin(), sk.begin() + skpv_length);
        std::vector<uint8_t>   pk_hash(sk.begin() + skpv_length + pk_length, sk.begin() + skpv_length + pk_length + pk_hash_length);
        secure_vector<uint8_t> z(sk.end() - z_length, sk.end());

        m_private = std::make_shared<Kyber_PrivateKeyInternal>(Internal::PolynomialVector::frombytes(skpv, mode.k()), std::move(pk_hash), std::move(z));
    }

    secure_vector<uint8_t> Kyber_PrivateKey::private_key_bits() const
    {
        auto pk = public_key_bits();
        const auto& pk_hash = m_private->public_key_hash();
        const auto& z = m_private->z();

        auto sk = m_private->polynomials().tobytes<secure_vector<uint8_t>>(m_mode.k());
        sk.insert(sk.end(), pk.begin(), pk.end());
        sk.insert(sk.end(), pk_hash.begin(), pk_hash.end());
        sk.insert(sk.end(), z.begin(), z.end());

        return sk;
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
        auto pub_key_alice = Kyber_PublicKey( this->public_key_bits(), KyberMode::Kyber512 ); // TO DO: no hard coded mode
        PK_KEM_Encryptor encryptor_bob( pub_key_alice, rng );

        secure_vector<uint8_t> cipher_text, key_bob;
        encryptor_bob.encrypt( cipher_text, key_bob, 32, rng );

        PK_KEM_Decryptor decryptor_bob( *this, rng );
        auto key_alice = decryptor_bob.decrypt( cipher_text.data(), cipher_text.size(), 32 );

        return key_alice == key_bob;
    }
}