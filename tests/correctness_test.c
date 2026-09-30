#include <assert.h>
#include <errno.h>
#include <stdio.h>

static char route_marker[] = "test-route";

#define CHECK(cond) do { \
  if (!(cond)) { \
    fprintf(stderr, "CHECK failed %s:%d: %s\n", __FILE__, __LINE__, #cond); \
    fflush(stderr); \
    abort(); \
  } \
} while (0)

static char *write_temp(const char *text) {
  char path[] = "/tmp/chinadns-XXXXXX";
  int fd = mkstemp(path);
  size_t len = strlen(text);
  CHECK(fd >= 0);
  CHECK(write(fd, text, len) == (ssize_t)len);
  CHECK(close(fd) == 0);
  return strdup(path);
}

static int load_route_text(const char *text) {
  char *path = write_temp(text);
  int rc;
  chnroute_file = path;
  rc = parse_chnroute();
  unlink(path);
  free(path);
  if (rc == 0)
    chnroute_file = route_marker;
  else
    chnroute_file = NULL;
  return rc;
}

static int ip_in(const char *ip) {
  struct in_addr addr;
  CHECK(inet_aton(ip, &addr) == 1);
  return test_ip_in_list(addr, &chnroute_list);
}

static int bound_udp(struct sockaddr_in *addr) {
  int fd = socket(AF_INET, SOCK_DGRAM, 0);
  socklen_t len = sizeof(*addr);
  CHECK(fd >= 0);
  memset(addr, 0, sizeof(*addr));
  addr->sin_family = AF_INET;
  addr->sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr->sin_port = 0;
  CHECK(bind(fd, (struct sockaddr *)addr, sizeof(*addr)) == 0);
  CHECK(getsockname(fd, (struct sockaddr *)addr, &len) == 0);
  return fd;
}

static ssize_t recv_ms(int fd, void *buf, size_t len, int ms) {
  fd_set readset;
  struct timeval tv;
  FD_ZERO(&readset);
  FD_SET(fd, &readset);
  tv.tv_sec = ms / 1000;
  tv.tv_usec = (ms % 1000) * 1000;
  if (select(fd + 1, &readset, NULL, NULL, &tv) <= 0)
    return -1;
  return recvfrom(fd, buf, len, 0, NULL, NULL);
}

static void reset_id_queue(void) {
  int i;
  for (i = 0; i < ID_ADDR_QUEUE_LEN; i++) {
    free(id_addr_queue[i].addr);
    id_addr_queue[i].addr = NULL;
    id_addr_queue[i].valid = 0;
    id_addr_queue[i].id = 0;
  }
  id_addr_queue_pos = 0;
}

static void reset_delay(void) {
  int i;
  for (i = 0; i < DELAY_QUEUE_LEN; i++) {
    if (delay_queue[i].in_use)
      free_delay(i);
  }
}

static void queue_client(uint16_t id, uint16_t old_id, const struct sockaddr_in *to) {
  struct sockaddr_in *stored = malloc(sizeof(*stored));
  id_addr_t entry;
  CHECK(stored != NULL);
  *stored = *to;
  memset(&entry, 0, sizeof(entry));
  entry.id = id;
  entry.old_id = old_id;
  entry.addr = (struct sockaddr *)stored;
  entry.addrlen = sizeof(*stored);
  entry.valid = 1;
  queue_add(entry);
}

static size_t put_qname(unsigned char *p, size_t off) {
  p[off++] = 3;
  memcpy(p + off, "www", 3);
  off += 3;
  p[off++] = 7;
  memcpy(p + off, "example", 7);
  off += 7;
  p[off++] = 3;
  memcpy(p + off, "com", 3);
  off += 3;
  p[off++] = 0;
  p[off++] = 0;
  p[off++] = 1;
  p[off++] = 0;
  p[off++] = 1;
  return off;
}

static size_t put_rr_header(unsigned char *p, size_t off, unsigned int type,
                            unsigned int rdlen) {
  p[off++] = 0xc0;
  p[off++] = 0x0c;
  p[off++] = 0x00;
  p[off++] = (unsigned char)type;
  p[off++] = 0x00;
  p[off++] = 0x01;
  p[off++] = 0x00;
  p[off++] = 0x00;
  p[off++] = 0x00;
  p[off++] = 60;
  p[off++] = (unsigned char)(rdlen >> 8);
  p[off++] = (unsigned char)rdlen;
  return off;
}

static size_t build_response(unsigned char *p, uint16_t id, int answers) {
  size_t off;
  int i;
  memset(p, 0, 512);
  p[0] = (unsigned char)(id >> 8);
  p[1] = (unsigned char)(id & 0xff);
  p[2] = 0x81;
  p[3] = 0x80;
  p[5] = 1;
  p[7] = (unsigned char)answers;
  off = put_qname(p, 12);
  for (i = 0; i < answers; i++) {
    p[off++] = 0xc0;
    p[off++] = 0x0c;
    p[off++] = 0x00;
    p[off++] = 0x01;
    p[off++] = 0x00;
    p[off++] = 0x01;
    p[off++] = 0x00;
    p[off++] = 0x00;
    p[off++] = 0x00;
    p[off++] = 60;
    p[off++] = 0x00;
    p[off++] = 4;
    p[off++] = 8;
    p[off++] = 8;
    p[off++] = 8;
    p[off++] = (unsigned char)(8 + i);
  }
  return off;
}

static size_t build_aaaa_then_foreign_a(unsigned char *p, uint16_t id) {
  size_t off;
  int i;
  memset(p, 0, 512);
  p[0] = (unsigned char)(id >> 8);
  p[1] = (unsigned char)(id & 0xff);
  p[2] = 0x81;
  p[3] = 0x80;
  p[5] = 1;
  p[7] = 2;
  off = put_qname(p, 12);
  off = put_rr_header(p, off, 28, 16);
  for (i = 0; i < 16; i++)
    p[off++] = 0x20;
  off = put_rr_header(p, off, 1, 4);
  p[off++] = 8;
  p[off++] = 8;
  p[off++] = 8;
  p[off++] = 8;
  return off;
}

static size_t build_aaaa_only(unsigned char *p, uint16_t id) {
  size_t off;
  int i;
  memset(p, 0, 512);
  p[0] = (unsigned char)(id >> 8);
  p[1] = (unsigned char)(id & 0xff);
  p[2] = 0x81;
  p[3] = 0x80;
  p[5] = 1;
  p[7] = 1;
  off = put_qname(p, 12);
  off = put_rr_header(p, off, 28, 16);
  for (i = 0; i < 16; i++)
    p[off++] = 0x20;
  return off;
}

static void send_packet(int remote_fd, const unsigned char *pkt, size_t len) {
  struct sockaddr_in dest;
  socklen_t dlen = sizeof(dest);
  int sender = socket(AF_INET, SOCK_DGRAM, 0);
  CHECK(sender >= 0);
  CHECK(getsockname(remote_fd, (struct sockaddr *)&dest, &dlen) == 0);
  CHECK(sendto(sender, pkt, len, 0, (struct sockaddr *)&dest, dlen) == (ssize_t)len);
  close(sender);
}

static void test_parser(void) {
  unsigned char bad[16];
  unsigned char query[64];
  ns_msg msg;
  size_t qlen;

  memset(bad, 0, sizeof(bad));
  bad[5] = 1;
  bad[12] = 0x41;
  CHECK(local_ns_initparse(bad, 13, &msg) == -1);

  memset(bad, 0, sizeof(bad));
  bad[5] = 1;
  bad[12] = 10;
  CHECK(local_ns_initparse(bad, 16, &msg) == -1);

  memset(query, 0, sizeof(query));
  query[5] = 1;
  qlen = put_qname(query, 12);
  CHECK(local_ns_initparse(query, (int)qlen, &msg) == 0);
  CHECK(ns_msg_count(msg, ns_s_qd) == 1);
}

static void test_mutate(void) {
  unsigned char query[64];
  unsigned char *big;
  unsigned char *dst;
  size_t qlen, off, out_len;
  int i;

  memset(query, 0, sizeof(query));
  query[5] = 1;
  qlen = put_qname(query, 12);
  dst = malloc(qlen + 1);
  CHECK(dst != NULL);
  CHECK(mutate_dns_query((char *)query, qlen, (char *)dst, qlen + 1, &out_len) == 1);
  CHECK(out_len == qlen + 1);
  CHECK(dst[qlen - 5] == 0xc0);
  CHECK(dst[qlen - 4] == 0x04);
  CHECK(mutate_dns_query((char *)query, qlen, (char *)dst, qlen, &out_len) == 0);
  free(dst);

  big = calloc(1, 512);
  CHECK(big != NULL);
  big[5] = 1;
  off = 12;
  for (i = 0; i < 7; i++) {
    big[off++] = 63;
    memset(big + off, 'a', 63);
    off += 63;
  }
  big[off++] = 46;
  memset(big + off, 'b', 46);
  off += 46;
  big[off++] = 0;
  big[off++] = 0;
  big[off++] = 1;
  big[off++] = 0;
  big[off++] = 1;
  CHECK(off == 512);
  dst = malloc(513);
  CHECK(dst != NULL);
  CHECK(mutate_dns_query((char *)big, 512, (char *)dst, 513, &out_len) == 1);
  CHECK(out_len == 513);
  CHECK(mutate_dns_query((char *)big, 512, (char *)dst, 512, &out_len) == 0);
  free(dst);
  free(big);

  memset(query, 0, sizeof(query));
  query[5] = 1;
  query[12] = 63;
  CHECK(mutate_dns_query((char *)query, 32, (char *)query, sizeof(query), &out_len) == 0);
}

static void test_queue_id_zero(void) {
  struct sockaddr_in *addr = calloc(1, sizeof(*addr));
  id_addr_t entry;
  id_addr_t *found;
  CHECK(addr != NULL);
  reset_id_queue();
  CHECK(queue_lookup(0) == NULL);
  addr->sin_family = AF_INET;
  memset(&entry, 0, sizeof(entry));
  entry.id = 0;
  entry.old_id = 7;
  entry.addr = (struct sockaddr *)addr;
  entry.addrlen = sizeof(*addr);
  queue_add(entry);
  found = queue_lookup(0);
  CHECK(found != NULL);
  CHECK(found->old_id == 7);
  CHECK(found->addr != NULL);
  CHECK(queue_lookup(1) == NULL);
  reset_id_queue();
}

static void test_routes(const char *repo_chnroute) {
  int i;
  CHECK(load_route_text("10.0.0.0/8\n10.1.2.0/24\n") == 0);
  CHECK(ip_in("10.2.0.1") == 1);
  CHECK(ip_in("10.1.2.1") == 1);
  CHECK(ip_in("10.1.2.255") == 1);
  CHECK(ip_in("11.0.0.1") == 0);
  CHECK(ip_in("9.255.255.255") == 0);

  CHECK(load_route_text("0.0.0.0/0\n") == 0);
  CHECK(ip_in("8.8.8.8") == 1);
  CHECK(ip_in("255.255.255.255") == 1);

  CHECK(load_route_text("128.0.0.0/1\n") == 0);
  CHECK(ip_in("128.0.0.1") == 1);
  CHECK(ip_in("255.255.255.255") == 1);
  CHECK(ip_in("127.255.255.255") == 0);

  CHECK(load_route_text("1.2.3.4/32\n") == 0);
  CHECK(ip_in("1.2.3.4") == 1);
  CHECK(ip_in("1.2.3.5") == 0);

  CHECK(load_route_text("1.2.3.4/33\n") != 0);
  CHECK(load_route_text("1.2.3.4/\n") != 0);
  CHECK(load_route_text("1.2.3.4/abc\n") != 0);
  CHECK(load_route_text("1.2.3.4/24abc\n") != 0);
  CHECK(load_route_text("1.2.3.4/24\n\n8.8.8.0/24\n") == 0);
  CHECK(ip_in("1.2.3.9") == 1);
  CHECK(ip_in("8.8.8.8") == 1);
  CHECK(chnroute_list.entries == 2);

  chnroute_file = (char *)repo_chnroute;
  CHECK(parse_chnroute() == 0);
  CHECK(chnroute_list.entries > 4000);
  for (i = 0; i < chnroute_list.entries; i++) {
    struct in_addr base = chnroute_list.nets[i].net;
    struct in_addr last;
    uint32_t last_host = ntohl(base.s_addr) | chnroute_list.nets[i].mask;
    last.s_addr = htonl(last_host);
    CHECK(test_ip_in_list(base, &chnroute_list) == 1);
    CHECK(test_ip_in_list(last, &chnroute_list) == 1);
  }
  CHECK(ip_in("223.255.252.1") == 1);
  CHECK(ip_in("223.255.253.255") == 1);
  CHECK(ip_in("223.255.254.1") == 0);
  CHECK(ip_in("1.0.1.1") == 1);
  CHECK(ip_in("8.8.8.8") == 0);
  CHECK(ip_in("0.0.0.1") == 0);
}

static void test_iplist(void) {
  char *path = write_temp("\n1.2.3.4\n");
  struct in_addr ip;
  ip_list_file = path;
  CHECK(parse_ip_list() == 0);
  CHECK(ip_list.entries == 1);
  CHECK(inet_aton("1.2.3.4", &ip) == 1);
  CHECK(bsearch(&ip, ip_list.ips, ip_list.entries, sizeof(ip), cmp_in_addr) != NULL);
  unlink(path);
  free(path);

  path = write_temp("not-an-ip\n");
  ip_list_file = path;
  CHECK(parse_ip_list() != 0);
  unlink(path);
  free(path);
  ip_list_file = NULL;
  free(ip_list.ips);
  ip_list.ips = NULL;
  ip_list.entries = 0;
}

static void test_delay_queue(void) {
  struct sockaddr_in dest;
  int recv_fd = bound_udp(&dest);
  int i;
  char buf[64];
  ssize_t n;
  const char payload_a[] = "delay-a";
  const char payload_b[] = "delay-b";

  local_sock = socket(AF_INET, SOCK_DGRAM, 0);
  CHECK(local_sock >= 0);
  reset_delay();
  empty_result_delay = 10.0f;
  schedule_delay(1, payload_a, sizeof(payload_a), (struct sockaddr *)&dest, sizeof(dest));
  schedule_delay(2, payload_b, sizeof(payload_b), (struct sockaddr *)&dest, sizeof(dest));
  for (i = 0; i < DELAY_QUEUE_LEN; i++) {
    if (delay_queue[i].in_use && delay_queue[i].id == 2)
      delay_queue[i].ts.tv_sec -= 30;
  }
  schedule_delay(1, payload_a, sizeof(payload_a), (struct sockaddr *)&dest, sizeof(dest));
  check_and_send_delay();
  n = recv_ms(recv_fd, buf, sizeof(buf), 200);
  CHECK(n == (ssize_t)sizeof(payload_b));
  CHECK(memcmp(buf, payload_b, sizeof(payload_b)) == 0);
  CHECK(recv_ms(recv_fd, buf, sizeof(buf), 50) < 0);

  cancel_delay(1);
  for (i = 0; i < DELAY_QUEUE_LEN; i++) {
    if (delay_queue[i].in_use)
      delay_queue[i].ts.tv_sec -= 30;
  }
  check_and_send_delay();
  CHECK(recv_ms(recv_fd, buf, sizeof(buf), 50) < 0);
  close(recv_fd);
  close(local_sock);
  local_sock = -1;
  empty_result_delay = EMPTY_RESULT_DELAY;
}

static void test_remote_answers(void) {
  struct sockaddr_in client_addr;
  struct sockaddr_in remote_addr;
  int client = bound_udp(&client_addr);
  int remote = bound_udp(&remote_addr);
  unsigned char pkt[512];
  unsigned char buf[512];
  size_t plen;
  ssize_t n;
  int i;
  const char suspect[] = "SUSPECT";

  local_sock = socket(AF_INET, SOCK_DGRAM, 0);
  CHECK(local_sock >= 0);
  remote_sock = remote;
  CHECK(setnonblock(remote_sock) == 0);
  compression = 0;
  bidirectional = 0;
  verbose = 0;
  free(ip_list.ips);
  ip_list.ips = NULL;
  ip_list.entries = 0;
  chnroute_file = NULL;
  reset_delay();
  reset_id_queue();

  queue_client(0x1234, 0x00ab, &client_addr);
  schedule_delay(0x1234, suspect, sizeof(suspect),
                 (struct sockaddr *)&client_addr, sizeof(client_addr));
  plen = build_response(pkt, 0x1234, 2);
  {
    ns_msg msg;
    CHECK(local_ns_initparse(pkt, (int)plen, &msg) == 0);
    CHECK(ns_msg_count(msg, ns_s_an) == 2);
  }
  send_packet(remote, pkt, plen);
  dns_handle_remote();
  n = recv_ms(client, buf, sizeof(buf), 200);
  CHECK(n == (ssize_t)plen);
  CHECK(buf[0] == 0x00 && buf[1] == 0xab);
  for (i = 0; i < DELAY_QUEUE_LEN; i++) {
    if (delay_queue[i].in_use)
      delay_queue[i].ts.tv_sec -= 30;
  }
  check_and_send_delay();
  CHECK(recv_ms(client, buf, sizeof(buf), 50) < 0);

  reset_delay();
  reset_id_queue();
  queue_client(0x2222, 0x0009, &client_addr);
  plen = build_response(pkt, 0x2222, 1);
  send_packet(remote, pkt, plen);
  dns_handle_remote();
  CHECK(recv_ms(client, buf, sizeof(buf), 50) < 0);
  for (i = 0; i < DELAY_QUEUE_LEN; i++) {
    if (delay_queue[i].in_use)
      delay_queue[i].ts.tv_sec -= 30;
  }
  check_and_send_delay();
  n = recv_ms(client, buf, sizeof(buf), 200);
  CHECK(n == (ssize_t)plen);
  CHECK(buf[0] == 0x00 && buf[1] == 0x09);

  CHECK(load_route_text("127.0.0.0/8\n") == 0);
  dns_servers_len = 2;
  reset_delay();
  reset_id_queue();
  queue_client(0x3333, 0x0001, &client_addr);
  plen = build_response(pkt, 0x3333, 2);
  send_packet(remote, pkt, plen);
  dns_handle_remote();
  CHECK(recv_ms(client, buf, sizeof(buf), 50) < 0);
  for (i = 0; i < DELAY_QUEUE_LEN; i++)
    CHECK(!delay_queue[i].in_use);

  reset_delay();
  reset_id_queue();
  queue_client(0x4444, 0x0011, &client_addr);
  plen = build_aaaa_then_foreign_a(pkt, 0x4444);
  {
    ns_msg msg;
    CHECK(local_ns_initparse(pkt, (int)plen, &msg) == 0);
  }
  send_packet(remote, pkt, plen);
  dns_handle_remote();
  CHECK(recv_ms(client, buf, sizeof(buf), 50) < 0);

  reset_delay();
  reset_id_queue();
  queue_client(0x5555, 0x0012, &client_addr);
  plen = build_aaaa_only(pkt, 0x5555);
  send_packet(remote, pkt, plen);
  dns_handle_remote();
  n = recv_ms(client, buf, sizeof(buf), 200);
  CHECK(n == (ssize_t)plen);
  CHECK(buf[0] == 0x00 && buf[1] == 0x12);

  reset_id_queue();
  memset(pkt, 0, sizeof(pkt));
  pkt[5] = 1;
  plen = put_qname(pkt, 12);
  send_packet(remote, pkt, plen);
  dns_handle_remote();
  CHECK(recv_ms(client, buf, sizeof(buf), 50) < 0);

  close(client);
  close(remote);
  close(local_sock);
  local_sock = -1;
  remote_sock = -1;
  dns_servers_len = 0;
}

static void test_empty_question(void) {
  struct sockaddr_in client_addr;
  struct sockaddr_in local_addr;
  int client = bound_udp(&client_addr);
  int local = bound_udp(&local_addr);
  unsigned char pkt[12];
  int saved_len = dns_servers_len;

  memset(pkt, 0, sizeof(pkt));
  local_sock = local;
  dns_servers_len = 0;
  verbose = 1;
  CHECK(sendto(client, pkt, sizeof(pkt), 0, (struct sockaddr *)&local_addr,
               sizeof(local_addr)) == (ssize_t)sizeof(pkt));
  CHECK(setnonblock(local_sock) == 0);
  dns_handle_local();
  verbose = 0;
  dns_servers_len = saved_len;
  reset_id_queue();
  close(client);
  close(local);
  local_sock = -1;
}

static void test_dns_server_list(void) {
  int i;
  struct sockaddr_in *addr;
  char *servers;

  CHECK(load_route_text("127.0.0.0/8\n") == 0);
  compression = 0;
  servers = strdup("127.0.0.1,,8.8.8.8,");
  CHECK(servers != NULL);
  dns_servers = servers;
  CHECK(resolve_dns_servers() == 0);
  CHECK(dns_servers_len == 2);
  CHECK(has_chn_dns == 1);
  for (i = 0; i < dns_servers_len; i++)
    CHECK(dns_server_addrs[i].addr != NULL);
  free(servers);

  servers = strdup(",,");
  CHECK(servers != NULL);
  dns_servers = servers;
  CHECK(resolve_dns_servers() == -1);
  free(servers);

  compression = 1;
  chnroute_file = NULL;
  servers = strdup("8.8.8.8");
  CHECK(servers != NULL);
  dns_servers = servers;
  CHECK(resolve_dns_servers() == -1);
  free(servers);

  CHECK(load_route_text("127.0.0.0/8\n") == 0);
  compression = 1;
  servers = strdup("127.0.0.1,8.8.8.8");
  CHECK(servers != NULL);
  dns_servers = servers;
  CHECK(resolve_dns_servers() == 0);
  CHECK(dns_servers_len == 2);
  CHECK(has_chn_dns == 1);
  CHECK(dns_server_addrs[0].addr != NULL);
  CHECK(dns_server_addrs[1].addr != NULL);
  addr = (struct sockaddr_in *)dns_server_addrs[0].addr;
  CHECK(ntohl(addr->sin_addr.s_addr) == 0x7f000001);
  addr = (struct sockaddr_in *)dns_server_addrs[1].addr;
  CHECK(ntohl(addr->sin_addr.s_addr) == 0x08080808);
  free(servers);
  compression = 0;
  free_dns_servers();
  dns_servers = NULL;
}

static void run_unit_tests(const char *repo_chnroute) {
  compression = 0;
  bidirectional = 0;
  verbose = 0;
  printf("parser\n");
  test_parser();
  printf("mutate\n");
  test_mutate();
  printf("queue\n");
  test_queue_id_zero();
  printf("routes\n");
  test_routes(repo_chnroute);
  printf("iplist\n");
  test_iplist();
  printf("delay\n");
  test_delay_queue();
  printf("remote\n");
  test_remote_answers();
  printf("empty question\n");
  test_empty_question();
  printf("dns servers\n");
  test_dns_server_list();

  reset_id_queue();
  reset_delay();
  clear_chnroute();
  free(ip_list.ips);
  ip_list.ips = NULL;
  ip_list.entries = 0;
  free(hostname_buf);
  hostname_buf = NULL;
  hostname_buflen = 0;
  printf("all correctness tests passed\n");
}

int main(int argc, char **argv) {
  const char *route = argc > 1 ? argv[1] : "chnroute.txt";
  run_unit_tests(route);
  return 0;
}
