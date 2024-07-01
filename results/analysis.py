import matplotlib.pyplot as plt
import numpy as np

with open('AkkaSeqSmallResults.txt', 'r') as f:
    lines = f.readlines()


new_results = {}
old_results = {}
for line in lines:
    parts = line.split(",")
    problem_number = int(parts[0][74:78])
    if '[SUCCESS]' in line and parts[-2].isdigit(): time = int(parts[-2])
    elif 'TIMEOUT' in line: time = 600_000
    
    if "AKKABODGE" in parts[1]:
        old_results[problem_number] = time
    elif "AKKAsequoia" in parts[1]:
        new_results[problem_number] = time
    else: continue

differences = {
    problem_number: old_results[problem_number] - new_results[problem_number]
    for problem_number in new_results
}
mults = {
    problem_number: old_results[problem_number] / new_results[problem_number]
    for problem_number in new_results
}


# Plot the differences distribution 
bins = [i for i in range(-10_000, 50_000, 1000)]
plt.hist(np.clip(list(differences.values()), bins[0], bins[-1]), bins=bins)
plt.xlabel('Old time - new time (ms)')
plt.ylabel('Frequency')
plt.show()
# Plot the multiples distribution
mult_bins = [i/10 for i in range(0, 50)]
plt.hist(np.clip(list(mults.values()), mult_bins[0], mult_bins[-1]), bins=mult_bins)
plt.xlabel('Old time / new time (ms)')
plt.ylabel('Frequency')
plt.show()

# filter out problems where old version takes <= 3000ms
FILTER = 3000
print(f"Problems taking >3s and <timeout: {[
    problem_number
    for problem_number in differences
    if old_results[problem_number] > FILTER and old_results[problem_number] < 600_000

]}")
filtered_differences = {
    problem_number: differences[problem_number]
    for problem_number in differences
    if old_results[problem_number] > FILTER
}
filtered_mults = {
    problem_number: mults[problem_number]
    for problem_number in mults
    if old_results[problem_number] > FILTER
}


# Plot the differences distribution again
plt.hist(np.clip(list(filtered_differences.values()), bins[0], bins[-1]), bins=bins)
plt.xlabel('Old time - new time (ms)')
plt.ylabel('Frequency')
plt.show()
# Plot the multiples distribution
plt.hist(np.clip(list(filtered_mults.values()), mult_bins[0], mult_bins[-1]), bins=mult_bins)
plt.xlabel('Old time / new time (ms)')
plt.ylabel('Frequency')
plt.show()
