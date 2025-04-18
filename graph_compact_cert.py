# Convert raw OUTPUT into graph
import matplotlib.pyplot as plt

perc_list = []
reveals_list = []
cert_size_list = []
proof_size_list = []

f = open(f"zok_tests/compact_cert_field/output", 'r')
line = f.readline()
line = f.readline()
while line != "":
    # "--"
    line = f.readline()
    # perc
    line = f.readline().strip()
    perc_list.append(float(line))
    # reveal
    line = f.readline().strip()
    reveals_list.append(int(line))
    # proof_size
    line = f.readline().strip()
    cert_size_list.append(int(line))
    # "--"
    line = f.readline()
    # prover_time
    line = f.readline()
    # verifier_time
    line = f.readline()
    # proof_size
    line = f.readline().strip()
    proof_size_list.append(int(line))
    # compiler_time
    line = f.readline()
    # ""
    line = f.readline()

num_tests = len(perc_list)

fig, ax = plt.subplots(figsize=(10, 4))
x_data = [x for x in range(num_tests)]
ax.plot(x_data, cert_size_list, label="Certificate size", marker='o')
ax.plot(x_data, proof_size_list, label="CoBBl proof size", marker='o')
ax.legend(loc='upper left')

x_label_list = [""]
for i in range(num_tests):
    x_label_list.append("η = {:.0%}".format(perc_list[i]) + "\nχ = " + str(reveals_list[i]))
y_label_list = ["", "500kB", "1MB", "1.5MB", "2MB", "2.5MB"]

ax.set_xticklabels(x_label_list)
ax.set_yticklabels(y_label_list)
ax.set_xlabel("Valid Percentage / Number of Samples")
plt.savefig('graphs/fig_compact_cert.png')