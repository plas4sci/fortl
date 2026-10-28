from ipykernel.kernelapp import IPKernelApp

from .kernel import FortlKernel

IPKernelApp.launch_instance(kernel_class=FortlKernel)
