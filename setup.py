#!/usr/bin/env python

from setuptools import setup

setup(name='sassy',
      version='1.1.0',
      packages=['sassy'],
      include_package_data=True,
      # package_data={'sassy': ['library/*/*.json']},
      url='https://github.com/seaneberhard/sassy',
      license='MIT',
      author='Sean Eberhard',
      author_email='eberhard.math@gmail.com',
      description='tools for playing with set association schemes',
      install_requires=['tqdm']
      )
