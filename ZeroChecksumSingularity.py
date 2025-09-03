"""
UDP Zero-Checksum Singularity - Numerical Investigation
"""

import socket
import struct
import random
import time
import itertools
from collections import defaultdict, Counter
from typing import List, Tuple, Dict
import hashlib

def compute_checksum(data: bytes) -> int:
    """Compute UDP checksum using one's complement arithmetic."""
    if len(data) % 2:
        data += b'\x00'
    
    total = 0
    for i in range(0, len(data), 2):
        word = (data[i] << 8) + data[i + 1]
        total += word
        
    while total >> 16:
        total = (total & 0xFFFF) + (total >> 16)
    
    return (~total) & 0xFFFF

def create_pseudo_header(src_ip: str, dst_ip: str, udp_length: int) -> bytes:
    """Create IPv4 pseudo-header for UDP checksum."""
    pseudo = b''
    for part in src_ip.split('.'):
        pseudo += struct.pack('!B', int(part))
    for part in dst_ip.split('.'):
        pseudo += struct.pack('!B', int(part))
    pseudo += struct.pack('!BBH', 0, 17, udp_length)
    return pseudo

def find_zero_checksums(count: int = 100, max_attempts: int = 10000000) -> List[Dict]:
    """Find multiple packets that produce zero checksum."""
    results = []
    attempts = 0
    start_time = time.time()
    
    src_ips = ["127.0.0.1", "10.0.0.1", "192.168.1.1", "172.16.0.1"]
    dst_ips = ["127.0.0.1", "10.0.0.2", "192.168.1.2", "172.16.0.2"]
    
    while len(results) < count and attempts < max_attempts:
        src_ip = random.choice(src_ips)
        dst_ip = random.choice(dst_ips)
        src_port = random.randint(1024, 65535)
        dst_port = random.randint(1, 65535)
        
        data_len = random.randint(1, 20)
        data = bytes([random.randint(0, 255) for _ in range(data_len)])
        
        udp_length = 8 + len(data)
        udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
        pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
        checksum_data = pseudo_header + udp_header + data
        computed = compute_checksum(checksum_data)
        
        if computed == 0:
            results.append({
                'src_ip': src_ip,
                'dst_ip': dst_ip,
                'src_port': src_port,
                'dst_port': dst_port,
                'data': data.hex(),
                'data_len': len(data),
                'attempts_before': attempts,
                'time_to_find': time.time() - start_time
            })
            start_time = time.time()
        
        attempts += 1
    
    return results, attempts

def analyze_zero_checksum_patterns():
    """Analyze patterns in data that produces zero checksums."""
    print("=" * 60)
    print("ZERO CHECKSUM PATTERN ANALYSIS")
    print("=" * 60)
    
    results, total_attempts = find_zero_checksums(count=100)
    
    print(f"\nSearch Statistics:")
    print(f"  Total attempts: {total_attempts:,}")
    print(f"  Zero checksums found: {len(results)}")
    print(f"  Success rate: {len(results)/total_attempts:.8f}")
    print(f"  Expected rate: {1/65536:.8f}")
    print(f"  Ratio to expected: {(len(results)/total_attempts)/(1/65536):.4f}")
    
    # Port analysis
    src_ports = [r['src_port'] for r in results]
    dst_ports = [r['dst_port'] for r in results]
    
    print(f"\nPort Distribution:")
    print(f"  Source ports - Min: {min(src_ports)}, Max: {max(src_ports)}, Avg: {sum(src_ports)/len(src_ports):.1f}")
    print(f"  Dest ports - Min: {min(dst_ports)}, Max: {max(dst_ports)}, Avg: {sum(dst_ports)/len(dst_ports):.1f}")
    
    # Data length analysis
    data_lens = [r['data_len'] for r in results]
    len_counter = Counter(data_lens)
    
    print(f"\nData Length Distribution:")
    for length in sorted(len_counter.keys()):
        print(f"  {length:2d} bytes: {len_counter[length]:3d} occurrences ({len_counter[length]/len(results)*100:.1f}%)")
    
    # Attempts distribution
    attempts = [r['attempts_before'] for r in results]
    print(f"\nAttempts to Find Distribution:")
    print(f"  Min: {min(attempts):,}")
    print(f"  Max: {max(attempts):,}")
    print(f"  Avg: {sum(attempts)/len(attempts):,.1f}")
    print(f"  Median: {sorted(attempts)[len(attempts)//2]:,}")
    
    # Byte frequency in zero-checksum data
    all_bytes = []
    for r in results:
        data = bytes.fromhex(r['data'])
        all_bytes.extend(data)
    
    byte_counter = Counter(all_bytes)
    print(f"\nMost common bytes in zero-checksum payloads:")
    for byte_val, count in byte_counter.most_common(10):
        print(f"  0x{byte_val:02x}: {count:3d} occurrences ({count/len(all_bytes)*100:.2f}%)")
    
    return results

def test_specific_patterns():
    """Test specific bit patterns for zero checksum tendency."""
    print("\n" + "=" * 60)
    print("SPECIFIC PATTERN TESTING")
    print("=" * 60)
    
    patterns = {
        'all_zeros': bytes([0x00] * 8),
        'all_ones': bytes([0xFF] * 8),
        'alternating_01': bytes([0xAA] * 8),
        'alternating_10': bytes([0x55] * 8),
        'ascending': bytes(range(8)),
        'descending': bytes(range(255, 247, -1)),
        'powers_of_2': bytes([1, 2, 4, 8, 16, 32, 64, 128]),
        'fibonacci': bytes([1, 1, 2, 3, 5, 8, 13, 21]),
    }
    
    src_ip = "10.0.0.1"
    dst_ip = "10.0.0.2"
    
    for pattern_name, pattern_data in patterns.items():
        checksums = []
        for src_port in range(1000, 2000, 100):
            for dst_port in range(1000, 2000, 100):
                udp_length = 8 + len(pattern_data)
                udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
                pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
                checksum_data = pseudo_header + udp_header + pattern_data
                computed = compute_checksum(checksum_data)
                checksums.append(computed)
        
        zero_count = checksums.count(0)
        print(f"\n{pattern_name:15s}: {zero_count:3d} zeros out of {len(checksums)} ({zero_count/len(checksums)*100:.4f}%)")
        
        if zero_count > 0:
            print(f"  Zero checksum ports:", end="")
            for src_port in range(1000, 2000, 100):
                for dst_port in range(1000, 2000, 100):
                    udp_length = 8 + len(pattern_data)
                    udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
                    pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
                    checksum_data = pseudo_header + udp_header + pattern_data
                    if compute_checksum(checksum_data) == 0:
                        print(f" ({src_port},{dst_port})", end="")

def measure_checksum_distribution():
    """Measure distribution of all possible checksum values."""
    print("\n" + "=" * 60)
    print("CHECKSUM VALUE DISTRIBUTION")
    print("=" * 60)
    
    checksum_counts = defaultdict(int)
    total_packets = 100000
    
    for _ in range(total_packets):
        src_ip = f"{random.randint(1,254)}.{random.randint(0,255)}.{random.randint(0,255)}.{random.randint(1,254)}"
        dst_ip = f"{random.randint(1,254)}.{random.randint(0,255)}.{random.randint(0,255)}.{random.randint(1,254)}"
        src_port = random.randint(1, 65535)
        dst_port = random.randint(1, 65535)
        data_len = random.randint(1, 20)
        data = bytes([random.randint(0, 255) for _ in range(data_len)])
        
        udp_length = 8 + len(data)
        udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
        pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
        checksum_data = pseudo_header + udp_header + data
        computed = compute_checksum(checksum_data)
        checksum_counts[computed] += 1
    
    print(f"\nTotal packets tested: {total_packets:,}")
    print(f"Unique checksums seen: {len(checksum_counts):,}")
    print(f"Expected unique values: ~{total_packets * (1 - 1/2.71828)**(total_packets/65536):.0f}")
    
    # Find most and least common checksums
    sorted_checksums = sorted(checksum_counts.items(), key=lambda x: x[1], reverse=True)
    
    print(f"\nMost frequent checksums:")
    for checksum, count in sorted_checksums[:10]:
        print(f"  0x{checksum:04x}: {count:4d} times ({count/total_packets*100:.4f}%)")
    
    print(f"\nLeast frequent checksums (appeared only once):")
    singles = [cs for cs, count in checksum_counts.items() if count == 1]
    print(f"  Count: {len(singles)} ({len(singles)/65536*100:.2f}% of possible values)")
    
    # Statistical analysis
    counts = list(checksum_counts.values())
    avg_count = sum(counts) / len(counts)
    variance = sum((c - avg_count)**2 for c in counts) / len(counts)
    std_dev = variance ** 0.5
    
    print(f"\nDistribution Statistics:")
    print(f"  Mean frequency: {avg_count:.4f}")
    print(f"  Std deviation: {std_dev:.4f}")
    print(f"  Min frequency: {min(counts)}")
    print(f"  Max frequency: {max(counts)}")
    print(f"  Zero checksum count: {checksum_counts.get(0, 0)}")
    
    return checksum_counts

def collision_analysis():
    """Analyze how many different packets produce the same checksum."""
    print("\n" + "=" * 60)
    print("COLLISION ANALYSIS")
    print("=" * 60)
    
    checksum_to_packets = defaultdict(list)
    
    # Generate packets with fixed ports but varying data
    src_ip, dst_ip = "192.168.1.1", "192.168.1.2"
    src_port, dst_port = 12345, 80
    
    for i in range(10000):
        data = i.to_bytes(2, 'big') if i < 65536 else bytes([i % 256, (i // 256) % 256])
        udp_length = 8 + len(data)
        udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
        pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
        checksum_data = pseudo_header + udp_header + data
        computed = compute_checksum(checksum_data)
        checksum_to_packets[computed].append(data.hex())
    
    collision_counts = Counter(len(packets) for packets in checksum_to_packets.values())
    
    print(f"\nCollisions for {10000} packets:")
    for collision_size, count in sorted(collision_counts.items()):
        print(f"  {collision_size} packets → same checksum: {count} cases")
    
    # Show examples of maximum collisions
    max_collision_size = max(collision_counts.keys())
    max_collision_checksums = [cs for cs, pkts in checksum_to_packets.items() 
                                if len(pkts) == max_collision_size]
    
    if max_collision_checksums:
        example_cs = max_collision_checksums[0]
        print(f"\nExample of {max_collision_size} packets with checksum 0x{example_cs:04x}:")
        for pkt in checksum_to_packets[example_cs][:5]:
            print(f"  Data: {pkt}")

def performance_analysis():
    """Measure performance characteristics of checksum calculation."""
    print("\n" + "=" * 60)
    print("PERFORMANCE ANALYSIS")
    print("=" * 60)
    
    data_sizes = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 1400, 1500]
    iterations = 10000
    
    print(f"\nTiming for {iterations} iterations per size:")
    for size in data_sizes:
        data = bytes([random.randint(0, 255) for _ in range(size)])
        
        start = time.perf_counter()
        for _ in range(iterations):
            compute_checksum(data)
        elapsed = time.perf_counter() - start
        
        rate = iterations / elapsed
        ns_per_op = elapsed * 1e9 / iterations
        bytes_per_sec = size * iterations / elapsed / 1e6
        
        print(f"  {size:4d} bytes: {ns_per_op:7.1f} ns/op, {rate:10.0f} ops/sec, {bytes_per_sec:7.2f} MB/s")

def edge_case_testing():
    """Test edge cases and boundary conditions."""
    print("\n" + "=" * 60)
    print("EDGE CASE TESTING")
    print("=" * 60)
    
    test_cases = [
        ("Empty payload", b""),
        ("Single byte 0x00", b"\x00"),
        ("Single byte 0xFF", b"\xFF"),
        ("Two bytes 0x00", b"\x00\x00"),
        ("Two bytes 0xFF", b"\xFF\xFF"),
        ("Max UDP length", b"x" * 65527),
        ("Checksum overflow trigger", b"\xFF\xFF" * 100),
    ]
    
    src_ip, dst_ip = "10.0.0.1", "10.0.0.2"
    src_port, dst_port = 1234, 5678
    
    for name, data in test_cases[:6]:  # Skip max length for performance
        udp_length = 8 + len(data)
        udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
        pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
        checksum_data = pseudo_header + udp_header + data
        computed = compute_checksum(checksum_data)
        
        print(f"\n{name}:")
        print(f"  Data length: {len(data)} bytes")
        print(f"  Checksum: 0x{computed:04x}")
        print(f"  Is zero: {computed == 0}")
        if computed == 0:
            print(f"  Transmitted as: 0xFFFF")

def find_minimal_zero_checksum():
    """Find minimal packets that produce zero checksum."""
    print("\n" + "=" * 60)
    print("MINIMAL ZERO CHECKSUM PACKETS")
    print("=" * 60)
    
    for data_len in range(0, 10):
        found = False
        attempts = 0
        max_attempts = 1000000
        
        while not found and attempts < max_attempts:
            src_ip = f"{random.randint(1,254)}.{random.randint(1,254)}.{random.randint(1,254)}.{random.randint(1,254)}"
            dst_ip = f"{random.randint(1,254)}.{random.randint(1,254)}.{random.randint(1,254)}.{random.randint(1,254)}"
            src_port = random.randint(1, 65535)
            dst_port = random.randint(1, 65535)
            
            if data_len == 0:
                data = b""
            else:
                data = bytes([random.randint(0, 255) for _ in range(data_len)])
            
            udp_length = 8 + len(data)
            udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
            pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
            checksum_data = pseudo_header + udp_header + data
            computed = compute_checksum(checksum_data)
            
            if computed == 0:
                print(f"\n{data_len}-byte payload zero checksum found:")
                print(f"  Attempts: {attempts + 1:,}")
                print(f"  IPs: {src_ip} → {dst_ip}")
                print(f"  Ports: {src_port} → {dst_port}")
                if data:
                    print(f"  Data: {data.hex()}")
                found = True
            
            attempts += 1
        
        if not found:
            print(f"\n{data_len}-byte: No zero checksum in {max_attempts:,} attempts")

def systematic_search():
    """Systematically search for zero checksums in small parameter space."""
    print("\n" + "=" * 60)
    print("SYSTEMATIC SEARCH IN CONSTRAINED SPACE")
    print("=" * 60)
    
    src_ip, dst_ip = "10.0.0.1", "10.0.0.2"
    zero_configs = []
    
    # Search over ports with 1-byte payload
    for data_byte in range(256):
        data = bytes([data_byte])
        for src_port in range(1000, 1100):
            for dst_port in range(1000, 1100):
                udp_length = 8 + len(data)
                udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
                pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
                checksum_data = pseudo_header + udp_header + data
                computed = compute_checksum(checksum_data)
                
                if computed == 0:
                    zero_configs.append((src_port, dst_port, data_byte))
    
    print(f"\nFound {len(zero_configs)} zero-checksum configurations")
    print(f"Search space: 256 * 100 * 100 = {256 * 100 * 100:,} combinations")
    print(f"Hit rate: {len(zero_configs) / (256 * 100 * 100):.8f}")
    
    if zero_configs:
        print(f"\nFirst 10 configurations:")
        for src_port, dst_port, data_byte in zero_configs[:10]:
            print(f"  Ports {src_port}→{dst_port}, data: 0x{data_byte:02x}")

def statistical_validation():
    """Validate that zero checksum occurrence follows expected distribution."""
    print("\n" + "=" * 60)
    print("STATISTICAL VALIDATION")
    print("=" * 60)
    
    trials = 10
    samples_per_trial = 100000
    zero_counts = []
    
    print(f"\nRunning {trials} trials of {samples_per_trial:,} random packets each:")
    
    for trial in range(trials):
        zeros = 0
        for _ in range(samples_per_trial):
            src_ip = f"{random.randint(1,254)}.{random.randint(0,255)}.{random.randint(0,255)}.{random.randint(1,254)}"
            dst_ip = f"{random.randint(1,254)}.{random.randint(0,255)}.{random.randint(0,255)}.{random.randint(1,254)}"
            src_port = random.randint(1, 65535)
            dst_port = random.randint(1, 65535)
            data = bytes([random.randint(0, 255) for _ in range(random.randint(1, 10))])
            
            udp_length = 8 + len(data)
            udp_header = struct.pack('!HHHH', src_port, dst_port, udp_length, 0)
            pseudo_header = create_pseudo_header(src_ip, dst_ip, udp_length)
            checksum_data = pseudo_header + udp_header + data
            
            if compute_checksum(checksum_data) == 0:
                zeros += 1
        
        zero_counts.append(zeros)
        observed_rate = zeros / samples_per_trial
        print(f"  Trial {trial+1:2d}: {zeros:3d} zeros, rate: {observed_rate:.8f}")
    
    expected = samples_per_trial / 65536
    mean_zeros = sum(zero_counts) / len(zero_counts)
    variance = sum((z - mean_zeros)**2 for z in zero_counts) / len(zero_counts)
    std_dev = variance ** 0.5
    
    print(f"\nSummary Statistics:")
    print(f"  Expected zeros per trial: {expected:.4f}")
    print(f"  Observed mean: {mean_zeros:.4f}")
    print(f"  Standard deviation: {std_dev:.4f}")
    print(f"  Min zeros: {min(zero_counts)}")
    print(f"  Max zeros: {max(zero_counts)}")
    print(f"  Deviation from expected: {abs(mean_zeros - expected)/expected*100:.2f}%")

if __name__ == "__main__":
    # Run all analyses
    analyze_zero_checksum_patterns()
    test_specific_patterns()
    checksum_counts = measure_checksum_distribution()
    collision_analysis()
    performance_analysis()
    edge_case_testing()
    find_minimal_zero_checksum()
    systematic_search()
    statistical_validation()
    
    print("\n" + "=" * 60)
    print("ANALYSIS COMPLETE")
    print("=" * 60)
