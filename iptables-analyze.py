#!/usr/bin/python

import z3
import ipaddress
import socket

def rule_to_model(source_cidr, source_port, dest_cidr, dest_port, protocol):
    source_cidr_model, source_cidr_constraints = v4cidr_to_model_and_constraints(source_cidr, 'source_cidr')
    source_port_model, source_port_constraints = port_to_model_and_constraints(port, 'source_port')
    dest_cidr_model, dest_cidr_constraints = v4cidr_to_model_and_constraints(dest_cidr, 'dest_cidr')
    dest_port_model, dest_port_constraints = port_to_model_and_constraints(port, 'dest_port')
    protocol_model, protocol_constraints = protocol_to_model_and_constraints(protocol)

def protocol_to_model_and_constraints(protocol):
    model = z3.BitVec('protocol', 8)
    proto_number = socket.getprotobyname(protocol)
    return model, [model == proto_number]

def port_to_model_and_constraints(port, name):
    model = z3.BitVec(name, 16)
    return model, [model == port]

def v4cidr_to_model_and_constraints(raw_unicode_string, name):
    cidr = ipaddress.ip_network(raw_unicode_string)
    first_address = int(cidr[0])
    last_address  = int(cidr[-1])

    model = z3.BitVec(name, 32)
    return model, [model >= first_address, model <= last_address]

def main():
    s = z3.Solver()

    firewall = z3.Function('firewall', z3.BoolSort())

    s.add(source_ip_constraints)

    source_port_model = z3.BitVec('source_port_model', 16)

    s.add(source_port_model)

    dest_ip_model, dest_ip_constraints = v4cidr_to_model_and_constraints(u'192.168.1.100/32', 'dest_cidr')
    
    s.add(dest_ip_constraints)

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
