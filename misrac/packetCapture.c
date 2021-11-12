#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <net/if.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <errno.h>
#include <sys/time.h>
#include <stdint.h>
#include "packetCapture.h"
#include <assert.h>
int getSocket(void)
{
    int s = socket(PF_CAN, SOCK_RAW, CAN_RAW);

    struct ifreq ifr;
    const char *ifname = "vcan0";
    (void)strcpy(ifr.ifr_name, ifname);
    ioctl(s, SIOCGIFINDEX, &ifr);

    struct sockaddr_can addr;
    addr.can_family = AF_CAN;
    addr.can_ifindex = ifr.ifr_ifindex;

    int bind_status = bind(s, (struct sockaddr *)&addr, sizeof(addr));
    assert(bind_status != -1); // check bind error
    return s;
}

can_packet packetCapture(int fd)
{
    can_packet frame;
    // CAN packet capture
    read(fd, &frame, sizeof(can_packet));
    struct timeval tv;
    gettimeofday(&tv, NULL);
    frame.timestamp = (tv.tv_sec * 1000000) + tv.tv_usec;
    return frame;
}