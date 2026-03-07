# GPU Stress Test: The Titan Scan
n_titan = 2305843009213693951  # 2^61 - 1
path = [n_titan]
curr = n_titan
captured = False

for step in range(1, 1000):
    if (curr - 8) % 10 == 0:
        captured_at = step
        captured_val = curr
        captured = True
        break
    curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
    path.append(curr)
print(len(path))