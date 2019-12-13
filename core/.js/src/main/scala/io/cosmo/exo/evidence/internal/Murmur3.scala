package io.cosmo.exo.evidence.internal

object Murmur3 {

  /** 128 bits of state */
  final class LongPair(var val1: Long = 0L, val2: Long = 0L)

  def fmix64(k1: Long): Long = {
    var k = k1
    k ^= (k >>> 33)
    k *= 0xff51afd7ed558ccdL
    k ^= k >>> 33
    k *= 0xc4ceb9fe1a85ec53L
    k ^= k >>> 33
    k
  }

  /** Gets a long from a byte buffer in little endian byte order. */
  //    public static final long getLongLittleEndian(byte[] buf, int offset) {
  //        return     ((long)buf[offset+7]    << 56)   // no mask needed
  //                | ((buf[offset+6] & 0xffL) << 48)
  //                | ((buf[offset+5] & 0xffL) << 40)
  //                | ((buf[offset+4] & 0xffL) << 32)
  //                | ((buf[offset+3] & 0xffL) << 24)
  //                | ((buf[offset+2] & 0xffL) << 16)
  //                | ((buf[offset+1] & 0xffL) << 8)
  //                | ((buf[offset  ] & 0xffL));        // no shift needed
  //    }

//  def getLongLittleEndian(buf: Array[Byte], offset: Int): Long = {
//       var r1 = buf(offset + 0) & 0xFF
//
//      }


}
