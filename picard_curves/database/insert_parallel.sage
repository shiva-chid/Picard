# Install programs to Magma root directory for this to work
from picard_curves import PicardDatabase, PicardCurve

R.<x> = PolynomialRing(QQ)
pols = [
    x^4 + x + 1,
    x^4 + x + 2
];
print len(pols)

# Only use next two lines when first setting up:
#database = PicardDatabase([ ])
#save(database, 'picard_database')
database = load('picard_database')

@parallel(ncpus=4)
def step(f):
    global database
    try:
        print f
        Y = database.calculate_pol_fork(f, calccond = True)
        if type(Y) == type('str'):
            return database.calculate_pol_fork(f, calccond = False)
        return Y
    except:
        return database.calculate_pol_fork(f, calccond = False)

# Actual creation
Ys = [ ]
for tup in list(step(pols)):
    Y = tup[1]
    Ys.append(Y)

# Save computed curves separately just in case
save(Ys, 'picard_curves')
for Y in Ys:
     database.insert_curve(Y)

print database
#save(database, 'picard_database')
