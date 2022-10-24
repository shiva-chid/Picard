from setuptools import setup

setup(
   name='picard_curves',
   version='1.0',
   description='Picard curves and databases',
   author='Irene Bouw, Jeroen Sijsling, and Stefan Wewers',
   author_email='jeroen.sijsling@uni-ulm.de',
   packages=['picard_curves'],
   package_data={'picard_curves': ['magma/*']},
   install_requires=[ ],
)
