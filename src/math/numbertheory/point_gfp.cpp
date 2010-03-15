/*
* Arithmetic for point groups of elliptic curves over GF(p)
*
* (C) 2007 Martin Doering, Christoph Ludwig, Falko Strenzke
*     2008-2010 Jack Lloyd
*
* Distributed under the terms of the Botan license
*/

#include <botan/point_gfp.h>
#include <botan/numthry.h>
#include <botan/mp_core.h>

namespace Botan {

PointGFp::PointGFp(const CurveGFp& curve) :
   curve(curve),
   coord_x(0),
   coord_y(curve.get_r()),
   coord_z(0)
   {
   }

PointGFp::PointGFp(const CurveGFp& curve, const BigInt& x, const BigInt& y) :
   curve(curve)
   {
   const Modular_Reducer& mod_p = curve.mod_p();

   coord_x = mod_p.multiply(curve.get_r(), x);
   coord_y = mod_p.multiply(curve.get_r(), y);
   coord_z = mod_p.reduce(curve.get_r());
   }

void PointGFp::monty_mult(BigInt& z,
                          const BigInt& x, const BigInt& y,
                          MemoryRegion<word>& workspace) const
   {
   if(x.is_zero() || y.is_zero())
      {
      z = 0;
      return;
      }

   const BigInt& p = curve.get_p();
   const u32bit p_size = curve.get_p_words();
   const word p_dash = curve.get_p_dash();

   workspace.clear();

   bigint_mul(workspace, workspace.size(), 0,
              x.data(), x.size(), x.sig_words(),
              y.data(), y.size(), y.sig_words());

   bigint_monty_redc(workspace, workspace.size(),
                     p.data(), p_size, p_dash);

   z.get_reg().resize(p_size);
   copy_mem(z.get_reg().begin(), &workspace[p_size], p_size);
   }

void PointGFp::monty_sqr(BigInt& z, const BigInt& x,
                         MemoryRegion<word>& workspace) const
   {
   if(x.is_zero())
      {
      z = 0;
      return;
      }

   const BigInt& p = curve.get_p();
   const u32bit p_size = curve.get_p_words();
   const word p_dash = curve.get_p_dash();

   workspace.clear();

   bigint_sqr(workspace, workspace.size(), 0,
              x.data(), x.size(), x.sig_words());

   bigint_monty_redc(workspace, workspace.size(),
                     p.data(), p_size, p_dash);

   z.get_reg().resize(p_size);
   copy_mem(z.get_reg().begin(), &workspace[p_size], p_size);
   }

void PointGFp::add(const PointGFp& rhs,
                   Workspace& workspace)
   {
   if(is_zero())
      {
      coord_x = rhs.coord_x;
      coord_y = rhs.coord_y;
      coord_z = rhs.coord_z;
      return;
      }
   else if(rhs.is_zero())
      return;

   const BigInt& p = curve.get_p();

   MemoryRegion<word>& ws = workspace.ws_monty;
   std::vector<BigInt>& ws_bn = workspace.ws_bn;

   BigInt& rhs_z2 = ws_bn[0];
   BigInt& U1 = ws_bn[1];
   BigInt& S1 = ws_bn[2];

   BigInt& lhs_z2 = ws_bn[3];
   BigInt& U2 = ws_bn[4];
   BigInt& S2 = ws_bn[5];

   BigInt& H = ws_bn[6];
   BigInt& r = ws_bn[7];

   BigInt& x = ws_bn[8];
   BigInt& y = ws_bn[9];
   BigInt& z = ws_bn[10];

   monty_sqr(rhs_z2, rhs.coord_z, ws);
   monty_mult(U1, coord_x, rhs_z2, ws);
   monty_mult(S1, coord_y, monty_mult(rhs.coord_z, rhs_z2, ws), ws);

   monty_sqr(lhs_z2, coord_z, ws);
   monty_mult(U2, rhs.coord_x, lhs_z2, ws);
   monty_mult(S2, rhs.coord_y, monty_mult(coord_z, lhs_z2, ws), ws);

   H = U2 - U1;
   if(H.is_negative())
      H += p;

   r = S2 - S1;
   if(r.is_negative())
      r += p;

   if(H.is_zero())
      {
      if(r.is_zero())
         {
         mult2(workspace);
         return;
         }

      *this = PointGFp(curve); // setting myself to zero
      return;
      }

   monty_sqr(U2, H, ws);

   monty_mult(S2, U2, H, ws);

   monty_mult(U2, U1, U2, ws);

   monty_sqr(x, r, ws);
   x -= S2 + (U2 << 1);
   while(x.is_negative())
      x += p;

   U2 -= x;
   if(U2.is_negative())
      U2 += p;

   y = monty_mult(r, U2, ws) - monty_mult(S1, S2, ws);
   if(y.is_negative())
      y += p;

   monty_mult(z, monty_mult(coord_z, rhs.coord_z, ws), H, ws);

   coord_x = x;
   coord_y = y;
   coord_z = z;
   }

// arithmetic operators
PointGFp& PointGFp::operator+=(const PointGFp& rhs)
   {
   Workspace ws(curve.get_p_words());
   add(rhs, ws);
   return *this;
   }

PointGFp& PointGFp::operator-=(const PointGFp& rhs)
   {
   PointGFp minus_rhs = PointGFp(rhs).negate();

   if(is_zero())
      *this = minus_rhs;
   else
      *this += minus_rhs;

   return *this;
   }

PointGFp& PointGFp::operator*=(const BigInt& scalar)
   {
   Workspace ws(curve.get_p_words());

   if(scalar.abs() <= 2) // special cases for small values
      {
      u32bit value = scalar.abs().to_u32bit();

      if(value == 0)
         *this = PointGFp(curve); // set to zero point
      else if(value == 1)
         {
         if(scalar.is_negative())
            this->negate();
         }
      else if(value == 2)
         {
         this->mult2(ws);
         if(scalar.is_negative())
            this->negate();
         }

      return *this;
      }

   const u32bit scalar_bits = scalar.bits();

   const u32bit window_size = 4;

   std::vector<PointGFp> Ps((1 << window_size) - 1);
   Ps[0] = *this;
   if(scalar.is_negative())
      Ps[0].negate();

   for(u32bit i = 1; i != Ps.size(); ++i)
      {
      Ps[i] = Ps[i-1];

      if(i % 1 == 1)
         Ps[i].mult2(ws);
      else
         Ps[i].add(Ps[0], ws);
      }

   PointGFp H(this->curve); // create as zero
   u32bit bits_left = scalar_bits;

   while(bits_left >= window_size)
      {
      u32bit nibble = scalar.get_substring(bits_left - window_size, window_size);

      for(u32bit i = 0; i != window_size; ++i)
         H.mult2(ws);

      if(nibble)
         H.add(Ps[nibble-1], ws);

      bits_left -= window_size;
      }

   while(bits_left)
      {
      H.mult2(ws);
      if(scalar.get_bit(bits_left-1))
         H.add(Ps[0], ws);

      --bits_left;
      }

   if(scalar.is_negative())
      H.negate();

   *this = H;
   return *this;
   }

// *this *= 2
void PointGFp::mult2(Workspace& workspace)
   {
   if(is_zero())
      return;
   else if(coord_y.is_zero())
      {
      *this = PointGFp(curve); // setting myself to zero
      return;
      }

   const BigInt& p = curve.get_p();

   MemoryRegion<word>& ws = workspace.ws_monty;
   std::vector<BigInt>& ws_bn = workspace.ws_bn;

   BigInt& y_2 = ws_bn[0];
   BigInt& S = ws_bn[1];
   BigInt& z4 = ws_bn[2];
   BigInt& a_z4 = ws_bn[3];
   BigInt& M = ws_bn[4];
   BigInt& U = ws_bn[5];
   BigInt& x = ws_bn[6];
   BigInt& y = ws_bn[7];
   BigInt& z = ws_bn[8];

   monty_sqr(y_2, coord_y, ws);

   monty_mult(S, coord_x, y_2, ws);
   S <<= 2; // * 4
   while(S >= p)
      S -= p;

   monty_sqr(z4, monty_sqr(coord_z, ws), ws);
   monty_mult(a_z4, curve.get_a_r(), z4, ws);

   M = 3 * monty_sqr(coord_x, ws) + a_z4;
   while(M >= p)
      M -= p;

   x = monty_sqr(M, ws) - (S << 1);
   while(x.is_negative())
      x += p;

   U = monty_sqr(y_2, ws);
   U <<= 3;
   while(U >= p)
      U -= p;

   S -= x;
   while(S.is_negative())
      S += p;

   y = monty_mult(M, S, ws) - U;
   if(y.is_negative())
      y += p;

   monty_mult(z, coord_y, coord_z, ws);
   z <<= 1;
   if(z >= p)
      z -= p;

   coord_x = x;
   coord_y = y;
   coord_z = z;
   }

BigInt PointGFp::get_affine_x() const
   {
   if(is_zero())
      throw Illegal_Transformation("Cannot convert zero point to affine");

   const Modular_Reducer& mod_p = curve.mod_p();

#if 1
   BigInt x = mod_p.multiply(curve.get_r_inv(), coord_x);
   BigInt z = mod_p.multiply(curve.get_r_inv(), coord_z);

   BigInt z2 = mod_p.square(z);
   return mod_p.multiply(x, inverse_mod(z2, curve.get_p()));
#else

   SecureVector<word> ws(2 * (curve.get_p_words() + 2));

   BigInt z2 = monty_sqr(coord_z, ws);
   z2 = inverse_mod(z2, curve.get_p());
   z2 = mod_p.multiply(z2, curve.get_r());
   return monty_mult(coord_x, z2, ws);
#endif
   }

BigInt PointGFp::get_affine_y() const
   {
   if(is_zero())
      throw Illegal_Transformation("Cannot convert zero point to affine");

   const Modular_Reducer& mod_p = curve.mod_p();

#if 1
   BigInt y = mod_p.multiply(curve.get_r_inv(), coord_y);
   BigInt z = mod_p.multiply(curve.get_r_inv(), coord_z);

   BigInt z3 = mod_p.cube(z);
   return mod_p.multiply(y, inverse_mod(z3, curve.get_p()));
#else

   SecureVector<word> ws(2 * (curve.get_p_words() + 2));

   BigInt z3 = monty_mult(coord_z, monty_sqr(coord_z, ws), ws);
   z3 = inverse_mod(z3, curve.get_p());
   z3 = mod_p.multiply(z3, curve.get_r());
   return monty_mult(coord_y, z3, ws);
#endif
   }

void PointGFp::check_invariants() const
   {
   /*
   Is the point still on the curve?? (If everything is correct, the
   point is always on its curve; then the function will return
   silently. If Oskar managed to corrupt this object's state, then it
   will throw an exception.)
   */

   if(is_zero())
      return;

   const Modular_Reducer& mod_p = curve.mod_p();

   BigInt x = mod_p.multiply(curve.get_r_inv(), coord_x);
   BigInt y = mod_p.multiply(curve.get_r_inv(), coord_y);
   BigInt z = mod_p.multiply(curve.get_r_inv(), coord_z);

   BigInt y2 = mod_p.square(y);
   BigInt x3 = mod_p.cube(x);

   BigInt ax = mod_p.multiply(x, curve.get_a());

   if(z == 1)
      {
      if(mod_p.reduce(x3 + ax + curve.get_b()) != y2)
         throw Illegal_Point("Invalid ECP point: y^2 != x^3 + a*x + b");
      }

   BigInt z2 = mod_p.square(z);
   BigInt z3 = mod_p.multiply(z, z2);

   BigInt ax_z4 = mod_p.multiply(mod_p.multiply(z3, z), ax);

   BigInt b_z6 = mod_p.multiply(curve.get_b(), mod_p.square(z3));

   if(y2 != mod_p.reduce(x3 + ax_z4 + b_z6))
      throw Illegal_Point("Invalid ECP point: y^2 != x^3 + a*x*z^4 + b*z^6");
   }

// swaps the states of *this and other, does not throw!
void PointGFp::swap(PointGFp& other)
   {
   curve.swap(other.curve);
   coord_x.swap(other.coord_x);
   coord_y.swap(other.coord_y);
   coord_z.swap(other.coord_z);
   }

bool PointGFp::operator==(const PointGFp& other) const
   {
   if(get_curve() != other.get_curve())
      return false;

   // If this is zero, only equal if other is also zero
   if(is_zero())
      return other.is_zero();

   return (get_affine_x() == other.get_affine_x() &&
           get_affine_y() == other.get_affine_y());
   }

// encoding and decoding
SecureVector<byte> EC2OSP(const PointGFp& point, byte format)
   {
   if(point.is_zero())
      return SecureVector<byte>(1); // single 0 byte

   const u32bit p_bytes = point.get_curve().get_p().bytes();

   BigInt x = point.get_affine_x();
   BigInt y = point.get_affine_y();

   SecureVector<byte> bX = BigInt::encode_1363(x, p_bytes);
   SecureVector<byte> bY = BigInt::encode_1363(y, p_bytes);

   if(format == PointGFp::UNCOMPRESSED)
      {
      SecureVector<byte> result(2*p_bytes+1);
      result[0] = 4;

      result.copy(1, bX.begin(), p_bytes);
      result.copy(p_bytes+1, bY.begin(), p_bytes);
      return result;
      }
   else if(format == PointGFp::COMPRESSED)
      {
      SecureVector<byte> result(p_bytes+1);
      result[0] = 2;

      result.copy(1, bX.begin(), bX.size());

      if(y.get_bit(0))
         result[0] |= 1;

      return result;
      }
   else if(format == PointGFp::HYBRID)
      {
      SecureVector<byte> result(2*p_bytes+1);
      result[0] = 6;

      result.copy(1, bX.begin(), bX.size());
      result.copy(p_bytes+1, bY.begin(), bY.size());

      if(y.get_bit(0))
         result[0] |= 1;

      return result;
      }
   else
      throw Invalid_Argument("illegal point encoding format specification");
   }

namespace {

BigInt decompress_point(bool yMod2,
                        const BigInt& x,
                        const CurveGFp& curve)
   {
   BigInt xpow3 = x * x * x;

   BigInt g = curve.get_a() * x;
   g += xpow3;
   g += curve.get_b();
   g = g % curve.get_p();

   BigInt z = ressol(g, curve.get_p());

   if(z < 0)
      throw Illegal_Point("error during decompression");

   if(z.get_bit(0) != yMod2)
      z = curve.get_p() - z;

   return z;
   }

}

PointGFp OS2ECP(const byte data[], u32bit data_len,
                const CurveGFp& curve)
   {
   if(data_len <= 1)
      return PointGFp(curve); // return zero

   const byte pc = data[0];

   BigInt x, y;

   if(pc == 2 || pc == 3)
      {
      //compressed form
      x = BigInt::decode(&data[1], data_len - 1);

      bool yMod2 = ((pc & 0x01) == 1);
      y = decompress_point(yMod2, x, curve);
      }
   else if(pc == 4)
      {
      const u32bit l = (data_len - 1) / 2;

      // uncompressed form
      x = BigInt::decode(&data[1], l);
      y = BigInt::decode(&data[l+1], l);
      }
   else if(pc == 6 || pc == 7)
      {
      const u32bit l = (data_len - 1) / 2;

      // hybrid form
      x = BigInt::decode(&data[1], l);
      y = BigInt::decode(&data[l+1], l);

      bool yMod2 = ((pc & 0x01) == 1);

      if(decompress_point(yMod2, x, curve) != y)
         throw Illegal_Point("OS2ECP: Decoding error in hybrid format");
      }
   else
      throw Invalid_Argument("OS2ECP: Unknown format type");

   PointGFp result(curve, x, y);
   result.check_invariants();
   return result;
   }

}
