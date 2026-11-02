/-!
# MD5 and SHA-256 (#50)

The evaluators behind the black boxes `Text.md5` and `Text.sha256`
(`implemented_by`): the digest of a string's UTF-8 bytes, as lowercase hex,
which is what DuckDB's `md5` and `sha256` return (RFC 1321, FIPS 180-4).
-/

namespace Substrait.Digest

def hex (bytes : List UInt8) : String :=
  let digit (n : UInt8) : Char := "0123456789abcdef".toList[n.toNat]!
  String.ofList (bytes.flatMap fun b => [digit (b / 16), digit (b % 16)])

/-- The message padded to a multiple of 64 bytes: `0x80`, zeros, and the
length in bits as 8 bytes, little- or big-endian. -/
def pad (msg : ByteArray) (bigEndian : Bool) : Array UInt8 := Id.run do
  let mut out := msg.toList.toArray.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  let bits := msg.size * 8
  let len := (List.range 8).map fun i => (bits / 2 ^ (8 * i) % 256).toUInt8
  return out ++ (if bigEndian then len.reverse else len).toArray

def word (b : Array UInt8) (i : Nat) (bigEndian : Bool) : UInt32 :=
  let bs := (List.range 4).map fun k => (b[i + k]!).toUInt32
  let bs := if bigEndian then bs else bs.reverse
  bs.foldl (fun acc x => acc * 256 + x) 0

def bytes (w : UInt32) (bigEndian : Bool) : List UInt8 :=
  let le := (List.range 4).map fun k => (w >>> (8 * k).toUInt32 &&& 0xff).toUInt8
  if bigEndian then le.reverse else le

def rotl (x : UInt32) (n : Nat) : UInt32 := (x <<< n.toUInt32) ||| (x >>> (32 - n).toUInt32)
def rotr (x : UInt32) (n : Nat) : UInt32 := (x >>> n.toUInt32) ||| (x <<< (32 - n).toUInt32)

/-! ## MD5 -/

def md5K : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

def md5S : Array Nat := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

def md5 (s : String) : String := Id.run do
  let msg := pad s.toUTF8 false
  let mut h : Array UInt32 := #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]
  for blk in List.range (msg.size / 64) do
    let m := (List.range 16).toArray.map fun i => word msg (64 * blk + 4 * i) false
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    for i in List.range 64 do
      let (f, g) :=
        if i < 16 then ((b &&& c) ||| (~~~b &&& d), i)
        else if i < 32 then ((d &&& b) ||| (~~~d &&& c), (5 * i + 1) % 16)
        else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
        else (c ^^^ (b ||| ~~~d), (7 * i) % 16)
      let f := f + a + md5K[i]! + m[g]!
      a := d
      d := c
      c := b
      b := b + rotl f md5S[i]!
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d]
  return hex (h.toList.flatMap (bytes · false))

/-! ## SHA-256 -/

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def sha256 (s : String) : String := Id.run do
  let msg := pad s.toUTF8 true
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for blk in List.range (msg.size / 64) do
    let mut w := (List.range 16).toArray.map fun i => word msg (64 * blk + 4 * i) true
    for i in List.range' 16 48 do
      let s0 := rotr w[i - 15]! 7 ^^^ rotr w[i - 15]! 18 ^^^ (w[i - 15]! >>> 3)
      let s1 := rotr w[i - 2]! 17 ^^^ rotr w[i - 2]! 19 ^^^ (w[i - 2]! >>> 10)
      w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut v := h
    for i in List.range 64 do
      let (a, b, c, d, e, f, g, hh) := (v[0]!, v[1]!, v[2]!, v[3]!, v[4]!, v[5]!, v[6]!, v[7]!)
      let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let t1 := hh + s1 + ch + sha256K[i]! + w[i]!
      let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      v := #[t1 + s0 + maj, a, b, c, d + t1, e, f, g]
    h := (List.range 8).toArray.map fun i => h[i]! + v[i]!
  return hex (h.toList.flatMap (bytes · true))

#guard md5 "" == "d41d8cd98f00b204e9800998ecf8427e"
#guard md5 "The quick brown fox jumps over the lazy dog" == "9e107d9d372bb6826bd81d3542a419d6"
#guard sha256 "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard sha256 "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
-- More than one block, and a multi-byte character.
#guard sha256 (String.ofList (List.replicate 100 'a')) ==
  "2816597888e4a0d3a36b82b83316ab32680eb8f00f8cd3b904d681246d285a0e"
#guard md5 "é" == "66ddcd97cfdeabb2f6fb8a999b4bc76f"
#guard md5 (String.ofList (List.replicate 100 'a')) == "36a92cc94a9e0fa21f625f8bfb007adf"

end Substrait.Digest
