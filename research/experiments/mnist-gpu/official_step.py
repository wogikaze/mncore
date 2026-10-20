import os, sys
sys.path.insert(0, '.')
import numpy as np, torch
from torchvision import datasets
from fx_export.train import SimpleNN1024, get_mnist_transform, init_globals
from fx_export.export import export_function
from fx_export.mncore_transform import transform_to_mncore
from fx_export.compile import generate_vsm_from_onnx
from fx_export.mncore_utils import assemble_vsm, extract_addresses_from_onnx
from fx_export.traincpp import train_emu, get_emu_output_info

HERE='research/experiments/mnist-gpu'
ref=np.load(f'{HERE}/reference.npz')
model=SimpleNN1024()
model.load_state_dict({k:torch.from_numpy(np.array(v)) for k,v in {
 'fc1.weight':ref['init_fc1.weight'],'fc1.bias':ref['init_fc1.bias'],
 'fc2.weight':ref['init_fc2.weight'],'fc2.bias':ref['init_fc2.bias']}.items()})
import fx_export.train as T
T.model=model
T.optimizer=torch.optim.SGD(model.parameters(), lr=0.01)
T.criterion=torch.nn.CrossEntropyLoss()

ds=datasets.MNIST('./data',train=True,download=False,transform=get_mnist_transform())
gen=torch.Generator().manual_seed(0)
loader=torch.utils.data.DataLoader(ds,batch_size=256,shuffle=True,drop_last=True,generator=gen)
data,target=next(iter(loader))
one=torch.utils.data.DataLoader(torch.utils.data.TensorDataset(data,target),batch_size=256,shuffle=False)

outdir=f'{HERE}/official'
os.makedirs(outdir,exist_ok=True)
func,dummy=T.get_example_function_and_inputs('train_step',256)
export_function(func,dummy,outdir,ignore_outputs=['loss'])
transform_to_mncore(f'{outdir}/model.onnx',f'{outdir}/mn_model.onnx')
vsm=generate_vsm_from_onnx(f'{outdir}/mn_model.onnx')
open(f'{outdir}/train.vsm','w').write(vsm)
assemble_vsm(f'{outdir}/train.vsm',f'{outdir}/train.asm')
asm=open(f'{outdir}/train.asm').read()
addresses=extract_addresses_from_onnx(f'{outdir}/mn_model.onnx')
output_info=get_emu_output_info(f'{outdir}/model.onnx',True)
loss=train_emu(model,one,asm,addresses,output_info,256,True,None)
print('loss',loss)
for k in ['fc2.weight','fc2.bias','fc1.weight','fc1.bias']:
    got=model.state_dict()[k].detach().numpy().ravel()
    want=ref['step1_'+k].ravel()
    print(k,'maxdiff',np.abs(got-want).max(),'gpu_ref_first',got[:3])
