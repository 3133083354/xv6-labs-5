#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "fs.h"
#include "sleeplock.h"
#include "file.h"
#include "net.h"

// xv6's ethernet and IP addresses
static uint8 local_mac[ETHADDR_LEN] = { 0x52, 0x54, 0x00, 0x12, 0x34, 0x56 };
static uint32 local_ip = MAKE_IP_ADDR(10, 0, 2, 15);

// qemu host's ethernet address.
static uint8 host_mac[ETHADDR_LEN] = { 0x52, 0x55, 0x0a, 0x00, 0x02, 0x02 };

static struct spinlock netlock;


#define MAX_QUEUE 16   
#define NQUEUE 32  

struct port_queue{
  int port;          
  int used;        
  char *buf[NQUEUE]; 
  int len[NQUEUE];  
  int head;         
  int tail;         
};

struct {
  struct spinlock lock;
  struct port_queue port_queues[MAX_QUEUE];
} port_table;

void
netinit(void)
{
  initlock(&netlock, "netlock");
  initlock(&port_table.lock, "port_table");
}

//
// bind(int port)
// prepare to receive UDP packets address to the port,
// i.e. allocate any queues &c needed.
//
uint64
sys_bind(void)
{
  int port;
  struct port_queue *p;

  argint(0, &port);
  acquire(&port_table.lock);

  for(p = port_table. port_queues; p< &port_table. port_queues[MAX_QUEUE]; p++){
    if(p->used && p->port == port){
      release(&port_table.lock);
      return -1;
    }
  }

  for(p = port_table.port_queues; p < &port_table.port_queues[MAX_QUEUE]; p++){
    if(!p->used){
      p->used = 1;
      p->port = port;
      p->head = 0;
      p->tail = 0;
      memset(p->buf, 0, sizeof(p->buf));
      release(&port_table.lock);
      return 0; 
    }
  }

  release(&port_table.lock);
  return -1; 
}

//
// unbind(int port)
// release any resources previously created by bind(port);
// from now on UDP packets addressed to port should be dropped.
//
uint64
sys_unbind(void)
{
  int port;
  struct port_queues *p;
  
  argint(0, &port);

  acquire(&port_table.lock);
  for(p = port_table.port_queues; p < &port_table.port_queues[MAX_QUEUE]; p++){
    if(p->used && p->port == port){
      p->used = 0;
      while(p->head != p->tail){
        if(p->buf[p->head])
          kfree(p->buf[p->head]);
        p->head = (p->head + 1) % NQUEUE;
      }
      release(&port_table.lock);
      return 0;
    }
  }
  release(&port_table.lock);
  return -1;
}

//
// recv(int dport, int *src, short *sport, char *buf, int maxlen)
// if there's a received UDP packet already queued that was
// addressed to dport, then return it.
// otherwise wait for such a packet.
//
uint64
sys_recv(void)
{
  int dport;
  uint64 src_addr, sport_addr, buf_addr;
  int maxlen;
  struct port_queue *p;
  char *pkt_buf;

  argint(0, &dport);         
  argaddr(1, &src_addr);    
  argaddr(2, &sport_addr);   
  argaddr(3, &buf_addr);   
  argint(4, &maxlen);     

  acquire(&port_table.lock);

  for(p =port_table.port_queues; p < &port_table.port_queues[MAX_QUEUE]; p++){
    if(p->used && p->port == dport)
      goto found; 
  }

  release(&port_table.lock);
  return -1; 

found:
  while(p->head == p->tail){
    sleep(p, &port_table.lock); 
  }

  pkt_buf = p->buf[p->head];
  p->buf[p->head] = 0; 
  p->head = (p->head + 1) % MAX_QUEUE; 

  release(&port_table.lock);

  struct eth *eth = (struct eth *)pkt_buf;
  struct ip *ip = (struct ip *)(eth + 1);
  struct udp *udp = (struct udp *)(ip + 1);
  char *payload = (char *)(udp + 1);

  int udp_len = ntohs(udp->ulen) - sizeof(struct udp);
  int copy_len = (udp_len < maxlen) ? udp_len : maxlen;

  struct proc *p1 = myproc();

  if(copyout(p1->pagetable, buf_addr, payload, copy_len) < 0){
    kfree(pkt_buf);
    return -1;
  }
  uint32 src_ip = ntohl(ip->ip_src);
  if(src_addr && copyout(p->pagetable, src_addr, (char*)&src_ip, sizeof(src_ip)) < 0){
    kfree(pkt_buf);
    return -1;
  }

  uint16 src_port = ntohs(udp->sport);
  if(sport_addr && copyout(p->pagetable, sport_addr, (char*)&src_port, sizeof(src_port)) < 0){
    kfree(pkt_buf);
    return -1;
  }

  kfree(pkt_buf);
  return copy_len;
}

// This code is lifted from FreeBSD's ping.c, and is copyright by the Regents
// of the University of California.
static unsigned short
in_cksum(const unsigned char *addr, int len)
{
  int nleft = len;
  const unsigned short *w = (const unsigned short *)addr;
  unsigned int sum = 0;
  unsigned short answer = 0;

  while (nleft > 1)  {
    sum += *w++;
    nleft -= 2;
  }

  if (nleft == 1) {
    *(unsigned char *)(&answer) = *(const unsigned char *)w;
    sum += answer;
  }

  sum = (sum & 0xffff) + (sum >> 16);
  sum += (sum >> 16);
  answer = ~sum;
  return answer;
}

//
// send(int sport, int dst, int dport, char *buf, int len)
//
uint64
sys_send(void)
{
  struct proc *p = myproc();
  int sport;
  int dst;
  int dport;
  uint64 bufaddr;
  int len;

  argint(0, &sport);
  argint(1, &dst);
  argint(2, &dport);
  argaddr(3, &bufaddr);
  argint(4, &len);

  int total = len + sizeof(struct eth) + sizeof(struct ip) + sizeof(struct udp);
  if(total > PGSIZE)
    return -1;

  char *buf = kalloc();
  if(buf == 0){
    printf("sys_send: kalloc failed\n");
    return -1;
  }
  memset(buf, 0, PGSIZE);

  struct eth *eth = (struct eth *) buf;
  memmove(eth->dhost, host_mac, ETHADDR_LEN);
  memmove(eth->shost, local_mac, ETHADDR_LEN);
  eth->type = htons(ETHTYPE_IP);

  struct ip *ip = (struct ip *)(eth + 1);
  ip->ip_vhl = 0x45; // version 4, header length 4*5
  ip->ip_tos = 0;
  ip->ip_len = htons(sizeof(struct ip) + sizeof(struct udp) + len);
  ip->ip_id = 0;
  ip->ip_off = 0;
  ip->ip_ttl = 100;
  ip->ip_p = IPPROTO_UDP;
  ip->ip_src = htonl(local_ip);
  ip->ip_dst = htonl(dst);
  ip->ip_sum = in_cksum((unsigned char *)ip, sizeof(*ip));

  struct udp *udp = (struct udp *)(ip + 1);
  udp->sport = htons(sport);
  udp->dport = htons(dport);
  udp->ulen = htons(len + sizeof(struct udp));

  char *payload = (char *)(udp + 1);
  if(copyin(p->pagetable, payload, bufaddr, len) < 0){
    kfree(buf);
    printf("send: copyin failed\n");
    return -1;
  }

  e1000_transmit(buf, total);

  return 0;
}

void
ip_rx(char *buf, int len)
{
  // don't delete this printf; make grade depends on it.
  static int seen_ip = 0;
  if(seen_ip == 0)
    printf("ip_rx: received an IP packet\n");
  seen_ip = 1;

  struct eth *eth = (struct eth *) buf;
  struct ip *ip = (struct ip *)(eth + 1);
  struct udp *udp = (struct udp *)(ip + 1);
  struct port_queues *p;

  if(ip->ip_p != IPPROTO_UDP) {
    kfree(buf); 
    return;
  }

  uint16 dport = ntohs(udp->dport);

  acquire(&port_table.lock);

  for(p = port_table.port_queues; p < &port_table.port_queues[MAX_QUEUE]; p++){
    if(p->used && p->port == dport){
      
      int next_tail = (p->tail + 1) % NQUEUE;
      if(next_tail == p->head){
        release(&port_table.lock);
        kfree(buf); 
        return;
      }

      p->buf[p->tail] = buf;
      p->len[p->tail] = len;
      p->tail = next_tail;

      wakeup(p);
      
      release(&port_table.lock);
      return; 
    }
  }

  release(&port_table.lock);
  
  kfree(buf);
}

//
// send an ARP reply packet to tell qemu to map
// xv6's ip address to its ethernet address.
// this is the bare minimum needed to persuade
// qemu to send IP packets to xv6; the real ARP
// protocol is more complex.
//
void
arp_rx(char *inbuf)
{
  static int seen_arp = 0;

  if(seen_arp){
    kfree(inbuf);
    return;
  }
  printf("arp_rx: received an ARP packet\n");
  seen_arp = 1;

  struct eth *ineth = (struct eth *) inbuf;
  struct arp *inarp = (struct arp *) (ineth + 1);

  char *buf = kalloc();
  if(buf == 0)
    panic("send_arp_reply");
  
  struct eth *eth = (struct eth *) buf;
  memmove(eth->dhost, ineth->shost, ETHADDR_LEN); // ethernet destination = query source
  memmove(eth->shost, local_mac, ETHADDR_LEN); // ethernet source = xv6's ethernet address
  eth->type = htons(ETHTYPE_ARP);

  struct arp *arp = (struct arp *)(eth + 1);
  arp->hrd = htons(ARP_HRD_ETHER);
  arp->pro = htons(ETHTYPE_IP);
  arp->hln = ETHADDR_LEN;
  arp->pln = sizeof(uint32);
  arp->op = htons(ARP_OP_REPLY);

  memmove(arp->sha, local_mac, ETHADDR_LEN);
  arp->sip = htonl(local_ip);
  memmove(arp->tha, ineth->shost, ETHADDR_LEN);
  arp->tip = inarp->sip;

  e1000_transmit(buf, sizeof(*eth) + sizeof(*arp));

  kfree(inbuf);
}

void
net_rx(char *buf, int len)
{
  struct eth *eth = (struct eth *) buf;

  if(len >= sizeof(struct eth) + sizeof(struct arp) &&
     ntohs(eth->type) == ETHTYPE_ARP){
    arp_rx(buf);
  } else if(len >= sizeof(struct eth) + sizeof(struct ip) &&
     ntohs(eth->type) == ETHTYPE_IP){
    ip_rx(buf, len);
  } else {
    kfree(buf);
  }
}