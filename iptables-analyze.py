#!/usr/bin/python

import z3
import ipaddress

def main():
    s = z3.Solver()

    source_cidr       = ipaddress.ip_network(u'192.168.0.0/16')

    # TODO: would a constrained bit-vector be a better representation?
    #source_ip         = source_cidr.network_address
    #source_prefix_len = source_cidr.prefixlen
    #source_ip_bin     = bin(int(source_ip))
    #source_model = z3.BitVec('source_model', 32)

    first_source = int(source_cidr[0])
    last_source  = int(source_cidr[-1])

    source_ip_model = z3.BitVec('source_ip_model', 32)
    s.add(source_ip_model >= first_source, source_ip_model <= last_source)

    source_port_model = z3.BitVec('source_port_model', 16)
    
    dest_cidr = ipaddress.ip_network(u'192.168.1.100/32')

    first_dest = int(dest_cidr[0])
    last_dest  = int(dest_cidr[-1])

    dest_ip_model = z3.BitVec('dest_ip_model', 32)
    s.add(dest_ip_model <= first_dest, dest_ip_model >= last_dest)

    dest_port_model = z3.BitVec('dest_port_model', 16)
    s.add(dest_port_model != 22)
    s.add(z3.Or(dest_port_model == 80, dest_port_model == 443))

    # create a new solving scope
    s.push()
    # verify a known good connection
    s.add(source_ip_model == int(ipaddress.IPv4Address(u'192.168.2.2')), source_port_model == 12345,
          dest_ip_model   == int(ipaddress.IPv4Address(u'192.168.1.100')), dest_port_model == 80)
    print s.check() # should print "sat", as in "these constraints are satisfiable"
    s.pop()

    s.push()
    # verify a known bad connection
    s.add(source_ip_model == int(ipaddress.IPv4Address(u'192.168.0.1')), source_port_model == 23456,
          dest_ip_model   == int(ipaddress.IPv4Address(u'192.168.1.101')), dest_port_model == 443)
    print s.check() # shoud print "unsat"
    s.pop()

if __name__ == "__main__":
    main()
