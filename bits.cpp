/* To compile, you need the zlib headers and pkgconfig and g++. Then

   g++ bits.cpp `pkg-config --cflags --libs zlib`

   It should also work with other compilers.
 */

#include <string>
#include <iostream>
#include <sstream>
#include <cstring>
#include <cstdlib>

#include <zlib.h>

int main (void) {
  char c;
  std::stringstream s;
  
  while (std::cin.get(c)) if ((c == '0') || (c == '1')) s << c;
  s.flush();

  std::string st = s.str();
  int stsize = st.size();
  int btsize = (stsize + 1) / 8;
  unsigned char* bits = new unsigned char[btsize];
  memset(bits, 0, btsize);

  int cbyte = 0;
  int cbit = 0;
  
  for (int i = 0; i < stsize; ++i) {
    char d = st[i];
    if (cbit == 8) {
      ++cbyte;
      cbit = 0;
    }
    
    if (d == '1') bits[cbyte] |= 1 << cbit;
    ++cbit;
  }

  // we assume no better compression ratio than 4
  unsigned char* out = new unsigned char[btsize*4];

  z_stream infstream;
  infstream.zalloc = Z_NULL;
  infstream.zfree = Z_NULL;
  infstream.opaque = Z_NULL;
  infstream.avail_in = (uInt) (cbyte + 1);
  infstream.next_in = (Bytef*)bits;
  infstream.avail_out = (uInt) (btsize * 4);
  infstream.next_out = (Bytef*)out;
  infstream.msg = Z_NULL;

  if (inflateInit2(&infstream, -15) != Z_OK) {
    std::cerr << "error initialising stream" << std::endl;
  }
  
  if (inflate(&infstream, Z_FINISH) != Z_STREAM_END) {
    std::cerr << "error:" <<
      (infstream.msg ? infstream.msg :
       "something is wrong, but no error message was provided by zlib") << std::endl;
    return EXIT_FAILURE;
  }
  inflateEnd(&infstream);

  for (char* c = (char*) out; c < (char*) infstream.next_out; ++c) {
    std::cout << *c;
  }

  std::cout << std::endl;
  delete [] bits;
  delete [] out;
}
