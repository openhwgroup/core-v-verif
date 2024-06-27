#ifndef REMOTE_BITBANG_H
#define REMOTE_BITBANG_H

#include <stdint.h>
#include <errno.h>

#include "jtag_dtm.h"

class remote_bitbang_t
{
public:
  // Create a new server, listening for connections from localhost on the given
  // port.
  remote_bitbang_t(uint16_t port, jtag_dtm_t *tap);

  // Do a bit of work.
  void tick();

  void tick(unsigned char * jtag_tck,
            unsigned char * jtag_tms,
            unsigned char * jtag_tdi,
            unsigned char * jtag_trstn,
            unsigned char jtag_tdo);

  unsigned char done() {return quit;}

  int exit_code() {return errno;}


private:
  jtag_dtm_t *tap;
  unsigned char tck;
  unsigned char tms;
  unsigned char tdi;
  unsigned char trstn;
  unsigned char tdo;
  unsigned char quit;

  int socket_fd;
  int client_fd;

  static const ssize_t buf_size = 64 * 1024;
  char recv_buf[buf_size];
  ssize_t recv_start, recv_end;

  // Check for a client connecting, and accept if there is one.
  void accept();
  // Execute any commands the client has for us.
  void execute_commands();

  void set_pins(char _tck, char _tms, char _tdi);
};

#endif
