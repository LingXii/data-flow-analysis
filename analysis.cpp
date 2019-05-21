#include<iostream>
#include<fstream>
#include<sstream>
#include<vector>
#include<string>
#include<cstdlib>
#include<cmath>
using namespace std;

/* Data structure */
const double inf=1/0.0;
int G_fcount=0;//ȫ�ֺ������� 
int G_lcount=0;//ȫ�־ֲ��������� 
int G_bcount=0;//ȫ�ֻ�������� 
int G_vcount=0;//ȫ�ֱ������� 
int G_ncount=0;//ȫ���������ڵ����
int G_pcount=-1;//ȫ��phi�������Ӽ���
int G_callcount=0;//ȫ�ֵ��ü��� 
int G_call=0;//���ú� 
int G_bb;//��ǰ������ 
int G_from;//���ԵĻ����� 
bool G_module=0;//�Ƿ��ڴ���һ������ 
bool G_link;//��ǰ����������һ�������Ƿ����� 
struct Phi_env
{
	int bid;
	int fid;
	int callid;
	Phi_env():bid(-1),fid(-1),callid(-1){} 
} G_phi_env;//phi�������� 

struct Range//��Χ 
{
	double lb,ub;//�½磬�Ͻ� 
	Range():lb(-inf),ub(inf){} 
	void operator= (Range r)//��Χ��ֵ
	{
		if(r.lb>r.ub)//�ռ� 
		{
			lb=inf;
			ub=-inf;
		} 
		else
		{
			lb=r.lb;
			ub=r.ub;
		}
	} 
	Range operator+ (Range r)//��Χ�ӷ� 
	{
		Range a;	
		if(lb>ub || r.lb>r.ub)
		{
			a.lb=inf;
			a.ub=-inf;
		} 	
		else
		{
			a.lb=lb+r.lb;
			a.ub=ub+r.ub;
		}		
		return a;
	}
	Range operator- (Range r)//��Χ���� 
	{
		Range a;
		if(lb>ub || r.lb>r.ub)
		{
			a.lb=inf;
			a.ub=-inf;
		} 	
		else
		{
			a.lb=lb-r.ub;
			a.ub=ub-r.lb;
		}	
		return a;
	}
	Range operator* (Range r)//��Χ�˷� 
	{
		Range a;
		if(lb>ub || r.lb>r.ub)
		{
			a.lb=inf;
			a.ub=-inf;
		} 	
		else
		{
			a.lb=min(min(lb*r.lb,ub*r.ub),min(lb*r.ub,ub*r.lb));
			a.ub=max(max(lb*r.lb,ub*r.ub),max(lb*r.ub,ub*r.lb));
		}	
		return a;
	}
	Range operator/ (Range r)//��Χ������� 
	{
		Range a;
		if(lb>ub || r.lb>r.ub)
		{
			a.lb=inf;
			a.ub=-inf;
		} 
		else
		{
			if(r.lb<=0 && r.ub>=0)
			{
				a.lb=-inf;
				a.ub=inf;
				return a;
			} 
			a.lb=min(min(lb/r.lb,ub/r.ub),min(lb/r.ub,ub/r.lb));
			a.ub=max(max(lb/r.lb,ub/r.ub),max(lb/r.ub,ub/r.lb));
		}				
		return a;
	} 
	Range operator% (Range r)//��Χ�������� 
	{
		Range a;
		if(lb>ub || r.lb>r.ub)
		{
			a.lb=inf;
			a.ub=-inf;
		} 
		else
		{
			if(r.lb<=0 && r.ub>=0)
			{
				a.lb=-inf;
				a.ub=inf;
				return a;
			} 
			int l=min(min(lb/r.lb,ub/r.ub),min(lb/r.ub,ub/r.lb));
			int u=max(max(lb/r.lb,ub/r.ub),max(lb/r.ub,ub/r.lb));
			a.lb=l;
			a.ub=u;
			return a;
		}						
	} 
};

struct Vari //���� 
{
	int id;
	int pos;//�ڷ��ű��е�λ��(local����ָ�򱻿��Ʒ�Χ�ı���) 
	int bid;//������ǰ��Ծ�Ļ����� 
	char stat;//�������ԣ�#Ϊ�̶���Χ��+������-�ݼ���*�����ּ� 
	bool type;//0Ϊint��1Ϊfloat 
	string name;
	Range range;
	Vari(int _id, int _type, string _name):
			id(_id),bid(-3),stat('#'),type(_type),name(_name){}
};

struct Sent//��� 
{
	int left_value;
	string arg1;
	string arg2;
	int op;//0none,1+,2-,3*,4/,5(int),6(float),7func,8phi,9ret 
	Sent(int _left,string _arg1,string _arg2,int _op):
			left_value(_left),arg1(_arg1),arg2(_arg2),op(_op){} 
};

struct Cond//�������� 
{
	string arg1;
	string arg2;
	int op;//1==,-1!=,2>,-2<=,3<,-3>=
	Cond(string _arg1,string _arg2,int _op):arg1(_arg1),arg2(_arg2),op(_op){} 
};

struct Edge //����������ӱ� 
{
	int s,t;//��㣬�յ� 
	Cond* cond;
	Edge(int _s, int _t):s(_s),t(_t){}
};

struct Basic //�����飬id:0Ϊ������ڣ�1Ϊ������� 
{
	int id;
	vector<int> entry;//��� 
	vector<int> exit;//���� 
	vector<Sent*> sent;//�������е���� 
	bool visit;//���ʱ�� 
	Edge* if_edge;
	Edge* else_edge;
	Basic(int _id):id(_id),if_edge(NULL),else_edge(NULL){}
};

struct Func//������ 
{
	int id;
	string name;
	vector<Vari*> local;//�ֲ��������ű� 
	vector<Vari*> vari;//������ 
	vector<Basic*> basic;//������� 
	vector<Edge*> edge; 
	Func(int _id, string _name):id(_id),name(_name)
	{
		basic.push_back(new Basic(0)); //�������� 
		basic.push_back(new Basic(1)); //������� 
	}
	void clear_tag()
	{
		for(vector<Basic*>::iterator it=basic.begin();it!=basic.end();it++)
			(*it)->visit=0;
	}
};
vector<Func*> func;//���к��� 
vector<Range> param_range;//����������Χ 
Func* env;//��ǰ������������ 

struct Flow//��������
{
	bool ctrl;//�Ƿ��п�������
	int lower;//�������½磬�������������ͼ�ڵ�ID��-1Ϊinf��-2Ϊ-inf 
	int upper;//�������Ͻ磬�������������ͼ�ڵ�ID��-1Ϊinf��-2Ϊ-inf  
	int next;//�������һ�ڵ�ID 
	bool strict;//��Χ�Ƿ��ϸ�����Ŀ��գ� 
	Flow(int _ctrl,int _next):ctrl(_ctrl),next(_next),strict(0){}
};

struct Node//������ͼ�ڵ�
{
	int id;
	int lid;//������λ�ã������Ϊ����1���ǽڵ�ID��
	int vid;//������λ�ã������Ϊ����2���ǽڵ�ID��
	int bid;//����������
	int fid;//��������
	int cid;//��������(phi�����б�ʾ�ſ���״̬��0ȫ����1�ҿ���-1�󿪣�-2��Ч) 
	double lb;//Լ���½�(phi�����б�ʾ��������ڻ�����)
	double ub;//Լ���Ͻ�(phi�����б�ʾ�ұ������ڻ�����)
	Range range;//�ڵ������Χ
	int op;//�ڵ�����
	vector<Flow*> flow;//���� 
	bool visit;
	Node(int _id,int _lid,int _vid,int _bid,int _fid):op(0),lb(-inf),ub(inf),
			id(_id),lid(_lid),vid(_vid),bid(_bid),fid(_fid),cid(G_call){} 
};

struct Data_flow_graph
{
	vector<Node*> node;//�������ڵ� 
	vector<vector<int> > phi_link;//phi�������� 
	void clear_tag()
	{
		for(vector<Node*>::iterator it=node.begin();it!=node.end();it++)
			(*it)->visit=0;
	}
}dfg;
Node* ret=NULL;//����ֵ�ڵ� 
vector<Node*> start;//��ʼ�ڵ� 

struct Tuple//һ�Ա��������ڼ�¼��֧ 
{
	int t1,t2;
	Vari* v1;
	Vari* v2;
	Tuple(int _t1,int _t2):t1(_t1),t2(_t2),v1(NULL),v2(NULL){} 
};
 
/* Function */
bool* btag;//��������ʱ�ǣ���find������ʹ�ã� 
int find_v(int vid, Basic* basic, Func* env)//�ҵ�֮ǰ����ı���Ϊvid�ı��� 
{
	btag[basic->id]=1;
	for(vector<Sent*>::iterator it=basic->sent.begin();it!=basic->sent.end();it++)
		if((*it)->left_value == vid) return basic->id;
	for(int i=0;i<basic->entry.size();i++)
	{
		if(!btag[basic->entry[i]])
		{
			int re=find_v(vid,env->basic[basic->entry[i]],env);
			if(re!=-1) return re;
		}
	} 
	return -1;
}

void build_data_flow(Func* env);
void connect_node(Basic* basic, Sent* sent, Func* env)//����������ͼ�ڵ� 
{
	switch(sent->op)
	{
		case 0://��ֵ 
		case 5://����ǿ��ת�� 
		case 6://����ǿ��ת�� 
		{
			Vari* v=env->vari[sent->left_value];
			Node* n;
			int nid=-1;
			for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
				if((*it)->vid==v->id && (*it)->bid==v->bid && (*it)->fid==env->id && (*it)->cid==G_call)
				{//������v�Ƿ�����������ͼ�� 
					nid=(*it)->id;
					n=dfg.node[nid];
					break;
				}
			if(nid==-1)//û�ҵ��������½ڵ� 
			{
				nid=G_ncount;
				n=new Node(nid,v->pos,v->id,basic->id,env->id);
				v->bid=basic->id;
				G_ncount++;
				dfg.node.push_back(n);
			}
			n->op=sent->op;
			Node* n2;
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				int nid2=G_ncount;				
				n2=new Node(nid2,-1,-1,basic->id,env->id);
				G_ncount++;
				dfg.node.push_back(n2);
				n2->range.lb=n2->range.ub=t;
				start.push_back(n2);			
			}
			else
			{
				Vari* v2=env->vari[atoi((sent->arg2).data())];
				int nid2=-1;
				for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
					if((*it)->vid==v2->id && (*it)->bid==v2->bid && (*it)->fid==env->id && (*it)->cid==G_call)
					{//������v2�Ƿ�����������ͼ�� 
						nid2=(*it)->id;
						n2=dfg.node[nid2];
						break;
					}
				if(nid2==-1)//û�ҵ��������½ڵ� 
				{
					nid2=G_ncount;
					n2=new Node(nid2,v2->pos,v2->id,basic->id,env->id);
					v2->bid=basic->id;
					G_ncount++;
					dfg.node.push_back(n2);
				}
			}
			n2->flow.push_back(new Flow(0,nid));//���ݴ�n2����n 
			break;
		}
		case 1://�ӷ� 
		case 2://����
		case 3://�˷�
		case 4://����
		{
			Vari* v=env->vari[sent->left_value];
			Node* n;
			int nid=-1;
			for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
				if((*it)->vid==v->id && (*it)->bid==v->bid && (*it)->fid==env->id && (*it)->cid==G_call)
				{//������v�Ƿ�����������ͼ�� 
					nid=(*it)->id;
					n=dfg.node[nid];
					break;
				}
			if(nid==-1)//û�ҵ��������½ڵ� 
			{
				nid=G_ncount;
				n=new Node(nid,v->pos,v->id,basic->id,env->id);
				v->bid=basic->id;
				G_ncount++;
				dfg.node.push_back(n);
			}
			Node* n1;
			if(sent->arg1[0]=='$')
			{
				double t=atof((sent->arg1).substr(1,(sent->arg1).length()-1).data());
				int nid1=G_ncount;				
				n1=new Node(nid1,-1,-1,basic->id,env->id);
				G_ncount++;
				dfg.node.push_back(n1);
				n1->range.lb=n1->range.ub=t;			
			}
			else
			{
				Vari* v1=env->vari[atoi((sent->arg1).data())];
				int nid1=-1;
				for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
					if((*it)->vid==v1->id && (*it)->bid==v1->bid && (*it)->fid==env->id && (*it)->cid==G_call)
					{//������v1�Ƿ�����������ͼ�� 
						nid1=(*it)->id;
						n1=dfg.node[nid1];
						break;
					}
				if(nid1==-1)//û�ҵ��������½ڵ� 
				{
					nid1=G_ncount;
					n1=new Node(nid1,v1->pos,v1->id,basic->id,env->id);
					v1->bid=basic->id;
					G_ncount++;
					dfg.node.push_back(n1);
				}
			}
			Node* n2;
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				int nid2=G_ncount;				
				n2=new Node(nid2,-1,-1,basic->id,env->id);
				G_ncount++;
				dfg.node.push_back(n2);
				n2->range.lb=n2->range.ub=t;			
			}
			else
			{
				Vari* v2=env->vari[atoi((sent->arg2).data())];
				int nid2=-1;
				for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
					if((*it)->vid==v2->id && (*it)->bid==v2->bid && (*it)->fid==env->id && (*it)->cid==G_call)
					{//������v2�Ƿ�����������ͼ�� 
						nid2=(*it)->id;
						n2=dfg.node[nid2];
						break;
					}
				if(nid2==-1)//û�ҵ��������½ڵ� 
				{
					nid2=G_ncount;
					n2=new Node(nid2,v2->pos,v2->id,basic->id,env->id);
					G_ncount++;
					v2->bid=basic->id;
					dfg.node.push_back(n2);
				}
			}
			int tempnid=G_ncount;
			Node* tempn=new Node(tempnid,n1->id,n2->id,-1,env->id);
			G_ncount++;
			dfg.node.push_back(tempn);
			tempn->op=sent->op;
			tempn->flow.push_back(new Flow(0,nid));
			n1->flow.push_back(new Flow(0,tempnid));
			n2->flow.push_back(new Flow(0,tempnid));
			break;
		}
		case 7://�������� 
		{
			G_callcount++;
			Vari* v=env->vari[sent->left_value];
			Node* n;
			int nid=-1;
			for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
				if((*it)->vid==v->id && (*it)->bid==v->bid && (*it)->fid==env->id && (*it)->cid==G_call)
				{//������v�Ƿ�����������ͼ�� 
					nid=(*it)->id;
					n=dfg.node[nid];
					break;
				}
			if(nid==-1)//û�ҵ��������½ڵ� 
			{
				nid=G_ncount;
				n=new Node(nid,v->pos,v->id,basic->id,env->id);
				v->bid=basic->id;
				G_ncount++;
				dfg.node.push_back(n);
			}
			int fid;
			for(int i=0;i<func.size();i++)//�ҵ������ú��� 
				if(func[i]->name == sent->arg1)
				{
					fid=i;
					break;
				}
			int old_call=G_call;
			G_call=G_callcount;
			build_data_flow(func[fid]);
			G_call=old_call;
			string args=sent->arg2;
			int c=0;
			int pos=0;
			while(1)
			{
				int i=pos;
				if(i>=args.length()) break;
				for(;args[i]!=';';i++);
				string arg=args.substr(pos,i-pos);
				Node* n1;
				if(arg[0]=='$')
				{
					double t=atof(arg.substr(1,arg.length()-1).data());
					int nid1=G_ncount;				
					n1=new Node(nid1,-1,-1,basic->id,env->id);
					G_ncount++;
					dfg.node.push_back(n1);
					n1->range.lb=n1->range.ub=t;			
				}
				else
				{
					Vari* v1=env->vari[atoi(arg.data())];
					int nid1=-1;
					for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
						if((*it)->vid==v1->id && (*it)->bid==v1->bid && (*it)->fid==env->id && (*it)->cid==G_call)
						{//������v1�Ƿ�����������ͼ�� 
							nid1=(*it)->id;
							n1=dfg.node[nid1];
							break;
						}
					if(nid1==-1)//û�ҵ��������½ڵ� 
					{
						nid1=G_ncount;
						n1=new Node(nid1,v1->pos,v1->id,basic->id,env->id);
						v1->bid=basic->id;
						G_ncount++;
						dfg.node.push_back(n1);
					}
				}
				Node* n2;
				Vari* v2=func[fid]->vari[func[fid]->local[c]->pos];
				int nid2=-1;
				for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
					if((*it)->vid==v2->id && (*it)->bid==v2->bid && (*it)->fid==fid && (*it)->cid==G_callcount)
					{//������v2�Ƿ�����������ͼ�� 
						nid2=(*it)->id;
						n2=dfg.node[nid2];
						break;
					}
				if(nid2==-1)//û�ҵ��������½ڵ� 
				{
					nid2=G_ncount;
					n2=new Node(nid2,v2->pos,v2->id,basic->id,env->id);
					G_ncount++;
					v2->bid=basic->id;
					dfg.node.push_back(n2);
				}
				n1->flow.push_back(new Flow(0,nid2));//������� 
				c++;
				pos=i+1;
			}
			ret->flow.push_back(new Flow(0,nid));//��������ֵ������ֵ 
			break;
		} 
		case 8://phi���� 
		{
			Vari* v=env->vari[sent->left_value];
			int pos=0,i;
			for(i=pos;sent->arg1[i]!=';';i++);
			Vari* v1=env->vari[atoi((sent->arg1).substr(pos,i-pos).data())];
			pos=i+1;
			for(i=pos;sent->arg1[i]!=';';i++);
			int from1=atoi((sent->arg1).substr(pos,i-pos).data());
			for(int i=0;i<env->basic.size();i++) btag[i]=0;
			from1=find_v(v1->id,env->basic[from1],env);
			pos=0;
			for(i=pos;sent->arg2[i]!=';';i++);
			Vari* v2=env->vari[atoi((sent->arg2).substr(pos,i-pos).data())];
			pos=i+1;
			for(i=pos;sent->arg2[i]!=';';i++);
			int from2=atoi((sent->arg2).substr(pos,i-pos).data());
			for(int i=0;i<env->basic.size();i++) btag[i]=0;
			from2=find_v(v2->id,env->basic[from2],env);
			Node* n;
			int nid=-1;
			for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
				if((*it)->vid==v->id && (*it)->bid==v->bid && (*it)->fid==env->id && (*it)->cid==G_call)
				{//������v�Ƿ�����������ͼ�� 
					nid=(*it)->id;
					n=dfg.node[nid];
					break;
				}
			if(nid==-1)//û�ҵ��������½ڵ� 
			{
				nid=G_ncount;
				n=new Node(nid,v->pos,v->id,basic->id,env->id);
				G_ncount++;
				v->bid=basic->id;
				dfg.node.push_back(n);
			}
			Node* n1;
			int nid1=-1;
			for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
				if((*it)->vid==v1->id && (*it)->bid==from1 && (*it)->fid==env->id && (*it)->cid==G_call)
				{//������v1�Ƿ�����������ͼ�� 
					nid1=(*it)->id;
					n1=dfg.node[nid1];
					break;
				}
			if(nid1==-1)//û�ҵ��������½ڵ� 
			{
				nid1=G_ncount;
				n1=new Node(nid1,v1->pos,v1->id,from1,env->id);
				G_ncount++;
				v1->bid=from1;
				dfg.node.push_back(n1);
			}
			Node* n2;
			int nid2=-1;
			for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
				if((*it)->vid==v2->id && (*it)->bid==from2 && (*it)->fid==env->id && (*it)->cid==G_call)
				{//������v2�Ƿ�����������ͼ�� 
					nid2=(*it)->id;
					n2=dfg.node[nid2];
					break;
				}
			if(nid2==-1)//û�ҵ��������½ڵ� 
			{
				nid2=G_ncount;
				n2=new Node(nid2,v2->pos,v2->id,from2,env->id);
				G_ncount++;
				v2->bid=from2;
				dfg.node.push_back(n2);
			}
			int tempnid=G_ncount;
			Node* tempn=new Node(tempnid,n1->id,n2->id,-1,env->id);
			tempn->cid=0;
			tempn->lb=from1;
			tempn->ub=from2;
			G_ncount++;
			dfg.node.push_back(tempn);
			tempn->op=sent->op;
			tempn->flow.push_back(new Flow(0,nid));
			n1->flow.push_back(new Flow(0,tempnid));
			n2->flow.push_back(new Flow(0,tempnid));
			//����phi��������
			if(G_phi_env.bid==basic->id && G_phi_env.fid==env->id && G_phi_env.callid==G_call)
			{
				vector<int> ve=dfg.phi_link[G_pcount];
				ve.push_back(tempnid);
				dfg.phi_link[G_pcount]=ve;
			} 
			else
			{
				G_pcount++;
				vector<int> ve;
				ve.push_back(tempnid);
				dfg.phi_link.push_back(ve);
			}
			G_phi_env.bid=basic->id;
			G_phi_env.fid=env->id;
			G_phi_env.callid=G_call;
			break;
		}
		case 9://return 
		{
			Vari* v=env->vari[sent->left_value];
			for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
				if((*it)->vid==v->id && (*it)->bid==v->bid && (*it)->fid==env->id && (*it)->cid==G_call)
				{
					ret=dfg.node[(*it)->id];
					break;
				}
			break;
		}
	}
}

Tuple condition_fork(Edge* edge, Func* env)//if���ж������ֲ� 
{
	Vari* v1;
	Vari* v2;
	if(edge->cond->arg1[0]=='$')
	{
		double t=atof((edge->cond->arg1).substr(1,(edge->cond->arg1).length()-1).data());
		v1=new Vari(-1,1,"const");
		v1->range.lb=v1->range.ub=t;	
	}
	else v1=env->vari[atoi((edge->cond->arg1).data())];
	if(edge->cond->arg2[0]=='$')
	{
		double t=atof((edge->cond->arg2).substr(1,(edge->cond->arg2).length()-1).data());
		v2=new Vari(-1,1,"const");
		v2->range.lb=v2->range.ub=t;	
	}
	else v2=env->vari[atoi((edge->cond->arg2).data())];
	switch(edge->cond->op)
	{
		case 1://==
		{
			if(v1->range.ub<v2->range.lb || v1->range.lb>v2->range.ub) return Tuple(0,0);
			break;
		}
		case 2://>
		{
			if(v1->range.ub<=v2->range.lb) return Tuple(0,0);
			break;
		}
		case 3://<
		{
			if(v1->range.lb>=v2->range.ub) return Tuple(0,0);
			break;
		}
		case -1://!=
		{
			if(v1->range.lb==v2->range.lb && v1->range.ub==v2->range.ub) return Tuple(0,0);
			break;
		}
		case -2://<=
		{
			if(v1->range.lb>v2->range.ub) return Tuple(0,0);
			break;
		}
		case -3://>=
		{
			if(v1->range.ub<v2->range.lb) return Tuple(0,0);
			break;
		}
	}	
	if(edge->cond->arg1[0]=='$') delete v1;
	if(edge->cond->arg2[0]=='$') delete v2;
	
	bool is_int=0;//�����ͱ��� 
	Tuple tuple(-1,-1);
	Node* n1;
	Node* n1_next;
	if(edge->cond->arg1[0]=='$')
	{
		double t=atof((edge->cond->arg1).substr(1,(edge->cond->arg1).length()-1).data());
		int nid1=G_ncount;				
		n1=new Node(nid1,-1,-1,edge->s,env->id);
		G_ncount++;
		dfg.node.push_back(n1);
		n1->range.lb=n1->range.ub=t;
		nid1=G_ncount;				
		n1_next=new Node(nid1,-1,-1,edge->t,env->id);
		G_ncount++;
		dfg.node.push_back(n1_next);
		n1_next->range.lb=n1_next->range.ub=t;			
	}
	else
	{
		Vari* v1=env->vari[atoi((edge->cond->arg1).data())];
		if(!v1->type) is_int=1;
		int nid1=-1;
		for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
			if((*it)->vid==v1->id && (*it)->bid==v1->bid && (*it)->fid==env->id && (*it)->cid==G_call)
			{//������v1�Ƿ�����������ͼ�� 
				nid1=(*it)->id;
				n1=dfg.node[nid1];
				break;
			}
		if(nid1==-1)//û�ҵ��������½ڵ� 
		{
			nid1=G_ncount;
			n1=new Node(nid1,v1->pos,v1->id,edge->s,env->id);
			G_ncount++;
			v1->bid=edge->s;
			dfg.node.push_back(n1);
		}
		nid1=-1;
		for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
			if((*it)->vid==v1->id && (*it)->bid==edge->t && (*it)->fid==env->id && (*it)->cid==G_call)
			{//������v1�Ƿ�����������ͼ�� 
				nid1=(*it)->id;
				n1_next=dfg.node[nid1];
				break;
			}
		if(nid1==-1)//û�ҵ��������½ڵ� 
		{
			nid1=G_ncount;
			n1_next=new Node(nid1,v1->pos,v1->id,edge->t,env->id);
			G_ncount++;
			dfg.node.push_back(n1_next);
		}
		tuple.t1=v1->bid;
		tuple.v1=v1;
		v1->bid=edge->t;
	}
	Flow* f1=new Flow(1,n1_next->id);
	n1->flow.push_back(f1);
	Node* n2;
	Node* n2_next;
	if(edge->cond->arg2[0]=='$')
	{
		double t=atof((edge->cond->arg2).substr(1,(edge->cond->arg2).length()-1).data());
		int nid2=G_ncount;				
		n2=new Node(nid2,-1,-1,edge->s,env->id);
		G_ncount++;
		dfg.node.push_back(n2);
		n2->range.lb=n2->range.ub=t;
		nid2=G_ncount;				
		n2_next=new Node(nid2,-1,-1,edge->s,env->id);
		G_ncount++;
		dfg.node.push_back(n2_next);
		n2_next->range.lb=n2_next->range.ub=t;			
	}
	else
	{
		Vari* v2=env->vari[atoi((edge->cond->arg2).data())];
		if(!v2->type) is_int=1;
		int nid2=-1;
		for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
			if((*it)->vid==v2->id && (*it)->bid==v2->bid && (*it)->fid==env->id && (*it)->cid==G_call)
			{//������v2�Ƿ�����������ͼ�� 
				nid2=(*it)->id;
				n2=dfg.node[nid2];
				break;
			}
		if(nid2==-1)//û�ҵ��������½ڵ� 
		{
			nid2=G_ncount;
			n2=new Node(nid2,v2->pos,v2->id,edge->s,env->id);
			G_ncount++;
			v2->bid=edge->s;
			dfg.node.push_back(n2);
		}
		nid2=-1;
		for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
			if((*it)->vid==v2->id && (*it)->bid==edge->t && (*it)->fid==env->id && (*it)->cid==G_call)
			{//������v2�Ƿ�����������ͼ�� 
				nid2=(*it)->id;
				n2_next=dfg.node[nid2];
				break;
			}
		if(nid2==-1)//û�ҵ��������½ڵ� 
		{
			nid2=G_ncount;
			n2_next=new Node(nid2,v2->pos,v2->id,edge->t,env->id);
			G_ncount++;
			dfg.node.push_back(n2_next);
		}
		tuple.t2=v2->bid;
		tuple.v2=v2;
		v2->bid=edge->t;
	}
	Flow* f2=new Flow(1,n2_next->id);
	n2->flow.push_back(f2);
	switch(edge->cond->op)
	{
		case 1://==
		{
			f1->lower=n2->id;
			f1->upper=n2->id;
			f2->lower=n1->id;
			f2->upper=n1->id;
			break;
		}
		case 2://>
		{
			f1->lower=n2->id;
			f1->upper=-1;
			if(is_int) f1->strict=1;
			f2->lower=-2;
			f2->upper=n1->id;
			if(is_int) f2->strict=1;
			break;
		}
		case 3://<
		{
			f1->lower=-2;
			f1->upper=n2->id;
			if(is_int) f1->strict=1;
			f2->lower=n1->id;
			f2->upper=-1;
			if(is_int) f2->strict=1;			
			break;
		}
		case -1://!=
		{
			f1->lower=-2;
			f1->upper=-1;
			f2->lower=-2;
			f2->upper=-1;
			break;
		}
		case -2://<=
		{
			f1->lower=-2;
			f1->upper=n2->id;
			f2->lower=n1->id;
			f2->upper=-1;			
			break;
		}
		case -3://>=
		{
			f1->lower=n2->id;
			f1->upper=-1;
			f2->lower=-2;
			f2->upper=n1->id;
			break;
		}
	}
	return tuple;	
}

void parse_vdef(bool type, string s, int pos)//��������������� 
{
	int i=pos;
	string name;
	for(;s[i]!=';';i++);
	name=s.substr(pos,i-pos);
	if(name.length()>1 && name[1]=='.') return;	
	cout<<"    put local: "<<G_lcount<<' '<<type<<' '<<name<<'\n';
	env->local.push_back(new Vari(G_lcount,type,name));
	G_lcount++;
}

void parse_goto(string s, int pos)//����goto��� 
{
	int i=pos;
	for(;s[i]!=' ';i++);
	pos=i+1;
	string id;
	for(i=pos;s[i]!='>';i++);
	id=s.substr(pos,i-pos);
	int bid=atoi(id.data());
	G_bcount=max(G_bcount,bid);	
	if(bid>G_bb)
	{
		cout<<"    put bb: "<<bid<<'\n';
		env->basic.resize(G_bcount+1);
		env->basic[bid]=new Basic(bid);
	}
	cout<<"    create edge: "<<G_bb<<"->"<<bid<<'\n';
	env->basic[G_bb]->exit.push_back(bid);
	env->basic[bid]->entry.push_back(G_bb);
	env->edge.push_back(new Edge(G_bb,bid));
	G_link=0;
}

void parse_bb(string s, int pos)//������������� 
{
	string id;
	int i=pos;
	for(;s[i]!='>';i++);
	id=s.substr(pos,i-pos);
	int bid=atoi(id.data());	
	if(bid>G_bcount || env->basic[bid]==NULL)
	{
		G_bcount=max(G_bcount,bid);
		cout<<"    put bb: "<<bid<<'\n';
		env->basic.resize(G_bcount+1);
		env->basic[bid]=new Basic(bid);
	}	
	if(G_link)
	{
		cout<<"    create edge: "<<G_bb<<"->"<<bid<<'\n';
	env->basic[G_bb]->exit.push_back(bid);
	env->basic[bid]->entry.push_back(G_bb);
	env->edge.push_back(new Edge(G_bb,bid));
	}
	G_bb=bid;
	G_link=1;
}

string put_vari(string s);
void parse_return(string s, int pos)//����return��� 
{
	cout<<"    create edge: "<<G_bb<<"->0\n";
	env->basic[G_bb]->exit.push_back(0);
	env->basic[0]->entry.push_back(G_bb);
	env->edge.push_back(new Edge(G_bb,0));
	if(pos<s.length())
	{
		int i=pos;
		for(;s[i]!=';';i++);
		string word=s.substr(pos,i-pos);
		int arg=atoi(put_vari(word).data());
		int op=9;
		cout<<"    put sentence: op"<<op<<' '<<arg<<'\n';
		env->basic[G_bb]->sent.push_back(new Sent(arg,"","",op));
	}
	G_module=0;
	
	cout<<"___________________graph______________________\n";
	for(vector<Basic*>::iterator it=env->basic.begin();it!=env->basic.end();it++)
	{
		cout<<"bb"<<(*it)->id<<": can get to ";
		for(vector<int>::iterator t=(*it)->exit.begin();t!=(*it)->exit.end();t++)
		{
			cout<<*t;
			if((*it)->if_edge!=NULL)
			{				
				if(*t==(*it)->if_edge->t) 
				{
					Cond* cond=(*it)->if_edge->cond;
					cout<<'('<<cond->arg1<<" op"<<cond->op<<' '<<cond->arg2<<") ";
				}	
				else
				{
					Cond* cond=(*it)->else_edge->cond;
					cout<<'('<<cond->arg1<<" op"<<cond->op<<' '<<cond->arg2<<") ";
				}					
			}
		}
		cout<<'\n';
		for(vector<Sent*>::iterator t=(*it)->sent.begin();t!=(*it)->sent.end();t++)
			cout<<"     "<<(*t)->left_value<<" = "<<(*t)->arg1<<" op"<<(*t)->op<<' '<<(*t)->arg2<<'\n';		
	}	
	cout<<"___________________graph______________________\n";
}

string put_vari(string s)//���������������ӱ��������ر���id 
{
	if((s[0]>='0'&&s[0]<='9')||s[0]=='-') return "c";//���� 
	int l=s.length();
	int i;
	for(i=0;i<l&&s[i]!='_';i++);
	if(i==l) return "f";//���� 
	string name=s.substr(0,i);
	int j;
	for(j=i+1;j<l&&s[j]!='(';j++);
	if(name.length()==0) name=s.substr(i,j-i);
	string id=s.substr(i+1,j-i-1);
	int vid=atoi(id.data());
	int type;
	int lid;
	for(vector<Vari*>::iterator it=env->local.begin();it!=env->local.end();it++)
		if((*it)->name==name) //�Ӻ����ľֲ����������ҵ��ñ����Ķ��� 
		{
			type=(*it)->type;
			lid=(*it)->id;
			break;
		}
	if(vid>G_vcount || env->vari[vid]==NULL)//����ñ����������ڣ�������������� 
	{
		G_vcount=max(G_vcount,vid);
		cout<<"    put variable: "<<vid<<' '<<type<<' '<<name<<' ';
		env->vari.resize(G_vcount+1);
		env->vari[vid]=new Vari(vid,type,name);
		env->vari[vid]->pos=lid;
		if(j<s.length()) env->local[lid]->pos=vid;//����ñ�����D��ǣ���������ָ�� 
		cout<<"\n";
	}	
	return id;
}

void parse_assign(string s, string left_v, int pos)//������ֵ��� 
{
	int left_value=atoi(put_vari(left_v).data());
	string word1;
	int op;
	int i=pos;
	for(;s[i]!=' '&&s[i]!=';';i++);
	word1=s.substr(pos,i-pos);
	string arg1=put_vari(word1);
	if(word1[0]=='(')//ǿת 
	{
		if(word1[1]=='i') op=5;//(int)
		else op=6;//(float)
		pos=i+1;
		int i=pos;
		for(;s[i]!=';';i++);
		string arg2=put_vari(s.substr(pos,i-pos));
		if(arg2=="c") arg2="$"+s.substr(pos,i-pos);//������'$'+��ֵ��ʾ 
		cout<<"    put sentence: "<<left_value<<" = op"<<op<<' '<<arg2<<'\n';
		env->basic[G_bb]->sent.push_back(new Sent(left_value,"",arg2,op));
		return; 
	}
	if(arg1=="f")//�������� 
	{
		op=7;
		pos=i+2;
		string arg2;
		while(1)
		{
			int j=pos;
			for(;s[j]!=','&&s[j]!=';';j++);
			if(s[j]==',') 
			{
				string param=s.substr(pos,j-pos);
				string arg=put_vari(param);
				if(arg=="c") arg="$"+param;
				arg2+=arg+";";
			}
			else
			{
				string param=s.substr(pos,j-pos-1);
				string arg=put_vari(param);
				if(arg=="c") arg="$"+param;
				arg2+=arg+";";
				break;
			}
			pos=j+2;
		}
		cout<<"    put sentence: "<<left_value<<" = "<<word1<<" op"<<op<<' '<<arg2<<'\n';
		env->basic[G_bb]->sent.push_back(new Sent(left_value,word1,arg2,op));
	}
	else//��ֵ��������� 
	{
		if(arg1=="c") arg1="$"+word1;
		if(s[i]==';')
		{
			op=0;			
			cout<<"    put sentence: "<<left_value<<" = op"<<op<<' '<<arg1<<'\n';
			env->basic[G_bb]->sent.push_back(new Sent(left_value,"",arg1,op));
			return;
		}
		switch(s[i+1])
		{
			case '+':op=1;break;
			case '-':op=2;break;
			case '*':op=3;break;
			case '/':op=4;break;
		}
		pos=i+3;
		int i=pos;
		for(;s[i]!=';';i++);
		string word2=s.substr(pos,i-pos);
		string arg2=put_vari(word2);
		if(arg2=="c") arg2="$"+word2;
		cout<<"    put sentence: "<<left_value<<" = "<<arg1<<" op"<<op<<' '<<arg2<<'\n';
		env->basic[G_bb]->sent.push_back(new Sent(left_value,arg1,arg2,op));
	}
}

void parse_phi(string s, int pos)//����phi������� 
{
	int op=8;
	int i=pos,j;
	for(;s[i]!=' ';i++);
	string word0=s.substr(pos,i-pos);
	int left_value=atoi(put_vari(word0).data());
	pos=i+8;
	for(i=pos;s[i]!=',';i++);
	for(j=i;s[j]!='(';j--);
	string word1=s.substr(pos,j-pos);
	string arg1=put_vari(word1)+";";
	string from1=s.substr(j+1,i-j-2);
	arg1+=from1+";";
	pos=i+2;
	for(i=pos;s[i]!='>';i++);
	for(j=i;s[j]!='(';j--);
	string word2=s.substr(pos,j-pos);
	string arg2=put_vari(word2)+";";
	string from2=s.substr(j+1,i-j-2);
	arg2+=from2+";";
	cout<<"    put sentence: "<<left_value<<" = "<<arg1<<" op"<<op<<' '<<arg2<<'\n';
	env->basic[G_bb]->sent.push_back(new Sent(left_value,arg1,arg2,op));
}

void parse_if(string s, int pos)//����if��� 
{
	int i=pos;
	for(;s[i]!=' ';i++);
	string word1=s.substr(pos,i-pos);
	string arg1=put_vari(word1);	
	if(arg1=="c") arg1="$"+word1;
	string symbol;
	int op;
	pos=i+1;
	for(i=pos;s[i]!=' ';i++);
	symbol=s.substr(pos,i-pos);
	if(symbol=="==") op=1;
	else if(symbol==">") op=2;
	else if(symbol=="<") op=3;
	else if(symbol=="!=") op=-1;
	else if(symbol=="<=") op=-2;
	else if(symbol==">=") op=-3;
	pos=i+1;
	for(i=pos;s[i]!=' ';i++);
	string word2=s.substr(pos,i-pos-1);
	string arg2=put_vari(word2);	
	if(arg2=="c") arg2="$"+word2;	
	
	pos=i+10;
	string id;
	for(i=pos;s[i]!='>';i++);
	id=s.substr(pos,i-pos);
	int bid=atoi(id.data());
	G_bcount=max(G_bcount,bid);	
	if(bid>G_bb)
	{
		cout<<"    put bb: "<<bid<<'\n';
		env->basic.resize(G_bcount+1);
		env->basic[bid]=new Basic(bid);
	}
	cout<<"    create edge: "<<G_bb<<"->"<<bid<<'\n';
	env->basic[G_bb]->exit.push_back(bid);
	env->basic[bid]->entry.push_back(G_bb);
	Edge* edge=new Edge(G_bb,bid);
	env->edge.push_back(edge);
	Cond* cond=new Cond(arg1,arg2,op);
	cout<<"    edge condition: "<<arg1<<" op"<<op<<' '<<arg2<<'\n';
	edge->cond=cond;
	env->basic[G_bb]->if_edge=edge;
	
	op=-op;
	pos=i+17;
	for(i=pos;s[i]!='>';i++);
	id=s.substr(pos,i-pos);
	bid=atoi(id.data());
	G_bcount=max(G_bcount,bid);	
	if(bid>G_bb)
	{
		cout<<"    put bb: "<<bid<<'\n';
		env->basic.resize(G_bcount+1);
		env->basic[bid]=new Basic(bid);
	}
	cout<<"    create edge: "<<G_bb<<"->"<<bid<<'\n';
	env->basic[G_bb]->exit.push_back(bid);
	env->basic[bid]->entry.push_back(G_bb);
	edge=new Edge(G_bb,bid);
	env->edge.push_back(edge);
	cond=new Cond(arg1,arg2,op);
	cout<<"    edge condition: "<<arg1<<" op"<<op<<' '<<arg2<<'\n';
	edge->cond=cond;
	env->basic[G_bb]->else_edge=edge;	
	G_link=0;
}

void parse_fdef(string s, string name, int pos)//��������������� 
{	
	env=new Func(G_fcount,name);
	func.push_back(env);
	G_fcount++;
	if(s[pos]==')') return;
	while(1)
	{
		int i=pos;
		for(;s[i]!=','&&s[i]!=')';i++);
		bool vtype;
		string vname;
		if(s[pos]=='i')//int�Ͳ��� 
		{
			vtype=0;
			vname=s.substr(pos+4,i-pos-4);
		}
		else//float�Ͳ��� 
		{
			vtype=1;
			vname=s.substr(pos+6,i-pos-6);
		}
		cout<<"    put local: "<<G_lcount<<' '<<vtype<<' '<<vname<<'\n';
		env->local.push_back(new Vari(G_lcount,vtype,vname));
		G_lcount++;
		if(s[i]==')') break;
		pos=i+2;
	}
}

void parse(string s)//����һ����� 
{
	int l=s.length();
	int i;
	string word1;//��ȡ����һ������ 
	for(i=0;i<l&&s[i]!=' ';i++);
	word1=s.substr(0,i);
	if(word1=="int") {parse_vdef(0,s,i+1); return;}//int�ͱ������� 
	if(word1=="float") {parse_vdef(1,s,i+1); return;}//float�ͱ������� 
	if(word1=="if") {parse_if(s,i+2); return;} //if��� 
	if(word1=="goto") {parse_goto(s,i+1); return;}//goto��� 
	if(word1=="#") {parse_phi(s,i+1); return;} //phi������� 
	if(word1[0]=='<')
	{
		if(word1=="<bb") {parse_bb(s,i+1); return;}//��������� 
		else 
		{
			string sbb;
			stringstream ss;
			ss<<G_bb+1;
			ss>>sbb;
			parse_bb(sbb+">;",0);
			return;
		} 
	}
	if(word1=="return"||word1=="return;") {parse_return(s,i+1); return;}//return��� 
	
	i++;
	int pos=i;
	string word2;
	for(;i<l&&s[i]!=' ';i++);
	word2=s.substr(pos,i-pos);
	if(word2=="=") parse_assign(s,word1,i+1);//��ֵ��� 
	else
	{
		if(G_module) return;//����������䣬�����д��� 
		else//����������� 
		{
			G_link=1;
			G_module=1;
			G_lcount=0;
			G_bcount=0;
			G_vcount=0;
			G_bb=1;
			parse_fdef(s,word1,pos+1);	
		}
	}
}

void remove_space(string& s)//ȥ�����ǰ�ÿո� 
{
	int i,j;
	for(i=0;s[i]==' ';i++);
	if(i==0) return;
	for(j=0;j+i<s.length();j++)
		s[j]=s[j+i];
	s.erase(j);
}

void visit_basic(Basic* basic, Func* env)//����һ�������� 
{
	basic->visit=1;
	for(vector<Sent*>::iterator it=basic->sent.begin();it!=basic->sent.end();it++)
		connect_node(basic,*it,env);
	Tuple tuple(0,0);
	if(basic->if_edge!=NULL)
	{//�����������������֧����������� 
		tuple=condition_fork(basic->if_edge,env);
		if(tuple.t1!=0 && tuple.t2!=0)			
			if(!env->basic[basic->if_edge->t]->visit) 
				visit_basic(env->basic[basic->if_edge->t],env);
		if(tuple.v1!=NULL) tuple.v1->bid=tuple.t1;
		if(tuple.v2!=NULL) tuple.v2->bid=tuple.t2;
		tuple=condition_fork(basic->else_edge,env);
		if(tuple.t1!=0 && tuple.t2!=0)
			if(!env->basic[basic->else_edge->t]->visit) 
				visit_basic(env->basic[basic->else_edge->t],env);
		if(tuple.v1!=NULL) tuple.v1->bid=tuple.t1;
		if(tuple.v2!=NULL) tuple.v2->bid=tuple.t2;
	}
	else if(basic->id!=0 && !env->basic[basic->exit[0]]->visit)
		visit_basic(env->basic[basic->exit[0]],env);
}

void build_data_flow(Func* env)//����������ͼ
{
	env->clear_tag();
	if(G_call==0) 
		for(int i=0;i<param_range.size();i++)//��ʼ��������Χ 
		{
			env->local[i]->range=param_range[i];
			int vpos=env->local[i]->pos;
			env->vari[vpos]->range=param_range[i];
		}
	visit_basic(env->basic[1],env);
	for(vector<Basic*>::iterator it=env->basic.begin();it!=env->basic.end();it++)
	{
		if(!(*it)->visit)
		{//�����Ƿ��п�����û�е���ĵط� 
			for(vector<Node*>::iterator t=dfg.node.begin();t!=dfg.node.end();t++)
			{
				if((*t)->op==8 && (*t)->lb==(*it)->id)
				{
					if((*t)->cid==0) (*t)->cid=1;
					if((*t)->cid==-1) (*t)->cid=-2;
				}
				if((*t)->op==8 && (*t)->ub==(*it)->id)
				{
					if((*t)->cid==0) (*t)->cid=-1;
					if((*t)->cid==1) (*t)->cid=-2;
				}
			}
		}
	}
}

void print_dfg()//���������ͼ
{
	cout<<"___________________dfg______________________\n";
	for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
	{
		cout<<(*it)->id;		
		if((*it)->op!=1 && (*it)->op!=2 && (*it)->op!=3 && (*it)->op!=4 && (*it)->op!=8)
		{//�����ڵ� 
			if((*it)->lid>=0) cout<<func[(*it)->fid]->local[(*it)->lid]->stat;
			cout<<": ";
			if((*it)->vid!=-1)
			{
				cout<<func[(*it)->fid]->local[(*it)->lid]->name<<'_'<<(*it)->vid;
				cout<<'('<<(*it)->fid<<'-'<<(*it)->bid<<')';
			} 
			else cout<<'$'<<(*it)->range.lb;
			cout<<" goto ";
			for(vector<Flow*>::iterator t=(*it)->flow.begin();t!=(*it)->flow.end();t++)
			{
				cout<<(*t)->next;
				if((*t)->ctrl) 
					cout<<'['<<(*t)->lower<<','<<(*t)->upper<<']';
				cout<<' ';
			}
		}
		else//����ڵ�
		{
			cout<<": ";
			switch((*it)->op)
			{
				case 1:cout<<'+';break;
				case 2:cout<<'-';break;
				case 3:cout<<'*';break;
				case 4:cout<<'/';break;
				case 8:cout<<"phi";break;
			}
			cout<<" goto ";
			for(vector<Flow*>::iterator t=(*it)->flow.begin();t!=(*it)->flow.end();t++)
			{
				cout<<(*t)->next;
				if((*t)->ctrl) 
					cout<<'['<<(*t)->lower<<','<<(*t)->upper<<']';
				cout<<' ';
			}
		} 
		cout<<"|range: ["<<(*it)->range.lb<<','<<(*it)->range.ub<<"]\n";
	}
	cout<<"___________________dfg______________________\n";
} 

void constrain(Func* env)//�������ص�Լ������
{
	Basic* basic=env->basic[0];
	while(1)
	{
		if(basic->id==1 || basic->entry.size()>1) break;
		int next=basic->id;
		basic=env->basic[basic->entry[0]];
		if(basic->if_edge != NULL)
		{
			Cond* cond;//���򷵻رض���������� 
			if(basic->if_edge->t==next) cond=basic->if_edge->cond;
			else cond=basic->else_edge->cond;
			bool is_int=0;//�����ͱ��� 
			vector<Node*> n1;
			vector<Node*> n2;
			if(cond->arg1[0]=='$')
			{
				double t=atof((cond->arg1).substr(1,(cond->arg1).length()-1).data());
				int nid1=G_ncount;	
				Node* node1=new Node(nid1,-1,-1,-1,env->id);			
				n1.push_back(node1);
				node1->range.lb=node1->range.ub=t;
			}
			else
			{
				Vari* v1=env->vari[atoi((cond->arg1).data())];
				if(!v1->type) is_int=1;
				int nid1=-1;
				for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
					if((*it)->op==0 && (*it)->vid==v1->id && (*it)->fid==env->id)
					{
						nid1=(*it)->id;
						n1.push_back(dfg.node[nid1]);
					}
			}
			if(cond->arg2[0]=='$')
			{
				double t=atof((cond->arg2).substr(1,(cond->arg2).length()-1).data());
				int nid2=G_ncount;		
				Node* node2=new Node(nid2,-1,-1,-1,env->id);		
				n2.push_back(node2);
				node2->range.lb=node2->range.ub=t;
			}
			else
			{
				Vari* v2=env->vari[atoi((cond->arg2).data())];
				if(!v2->type) is_int=1;
				int nid2=-1;
				for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
					if((*it)->op==0 && (*it)->vid==v2->id && (*it)->fid==env->id)
					{
						nid2=(*it)->id;
						n2.push_back(dfg.node[nid2]);
					}
			}
			switch(cond->op)
			{
				case 1://==
				{
					for(vector<Node*>::iterator i1=n1.begin();i1!=n1.end();i1++)
					{
						(*i1)->lb=n2[0]->range.lb;
						(*i1)->ub=n2[0]->range.ub;
						if(is_int) (*i1)->ub=floor((*i1)->ub+1);
						if(is_int) (*i1)->lb=ceil((*i1)->lb-1);
					}
					break;
				}
				case 2://>
				{
					for(vector<Node*>::iterator i1=n1.begin();i1!=n1.end();i1++)
					{
						(*i1)->lb=n2[0]->range.lb;
					}
					break;
				}
				case 3://<
				{
					for(vector<Node*>::iterator i1=n1.begin();i1!=n1.end();i1++)
					{
						(*i1)->ub=n2[0]->range.ub;
					}
					break;			
				}
				case -1://!=
				{
					break;
				}
				case -2://<=
				{
					for(vector<Node*>::iterator i1=n1.begin();i1!=n1.end();i1++)
					{
						(*i1)->ub=n2[0]->range.ub;
						if(is_int) (*i1)->ub=floor((*i1)->ub+1);
					}			
					break;
				}
				case -3://>=
				{
					for(vector<Node*>::iterator i1=n1.begin();i1!=n1.end();i1++)
					{
						(*i1)->lb=n2[0]->range.lb;
						if(is_int) (*i1)->lb=ceil((*i1)->lb-1);
					}
					break;
				}
			}
			if(cond->arg1[0]=='$') delete n1[0];
			if(cond->arg2[0]=='$') delete n2[0];	
		}
	}
} 

void phi_check()//phi������� 
{
	for(vector<vector<int> >::iterator it=dfg.phi_link.begin();it!=dfg.phi_link.end();it++)
	{
		if(it->size()>1)
		{
			bool close1=0, close2=0;
			int c=-1;
			for(vector<int>::iterator t=it->begin();t!=it->end();t++)
			{
				int nid1=dfg.node[*t]->lid;
				int nid2=dfg.node[*t]->vid;
				int next=dfg.node[*t]->flow[0]->next;
				if(dfg.node[next]->lb > dfg.node[nid1]->range.ub || 
						dfg.node[next]->ub < dfg.node[nid1]->range.lb)
				{
					close1=1;
					c=dfg.node[*t]->id;
				}
				if(dfg.node[next]->lb > dfg.node[nid2]->range.ub || 
						dfg.node[next]->ub < dfg.node[nid2]->range.lb)
				{
					close2=1;
					c=dfg.node[*t]->id;
				}
			}
			if(close1)
				for(vector<int>::iterator t=it->begin();t!=it->end();t++)
				{
					if(*t!=c) 
						dfg.node[*t]->cid=1;
				}
			if(close2)
				for(vector<int>::iterator t=it->begin();t!=it->end();t++)
				{
					if(*t!=c) dfg.node[*t]->cid=-1;	
				}
		}
	}
}

void flow_data(Node* node, bool rev)//������������ 
{
	node->visit=1;
	switch(node->op)
	{
		case 1:
		{
			Node* n1=dfg.node[node->lid];
			Node* n2=dfg.node[node->vid];			
			Node* next=dfg.node[node->flow[0]->next];
			if(rev)//���ݷ��� 
				if(node->range.lb<next->range.lb || node->range.ub<next->range.ub)
				{
					Range r1=next->range-n2->range;
					if(r1.lb>n1->range.lb) n1->range.lb=r1.lb;
					if(r1.ub<n1->range.ub) n1->range.ub=r1.ub;
					Range r2=next->range-n1->range;
					if(r2.lb>n2->range.lb) n2->range.lb=r2.lb;
					if(r2.ub<n2->range.ub) n2->range.ub=r2.ub;
				}
			node->range=n1->range+n2->range;
			if(n1->range.lb>=0)//n1������
			{
				if(n2->lid>=0 && func[n2->fid]->local[n2->lid]->stat=='#')
					func[n2->fid]->local[n2->lid]->stat='+';
				if(n2->lid>=0 && func[n2->fid]->local[n2->lid]->stat=='-')
					func[n2->fid]->local[n2->lid]->stat='*';
			} 
			else if(n1->range.ub<=0)//n1�Ǹ���
			{
				if(n2->lid>=0 && func[n2->fid]->local[n2->lid]->stat=='#')
					func[n2->fid]->local[n2->lid]->stat='-';
				if(n2->lid>=0 && func[n2->fid]->local[n2->lid]->stat=='+')
					func[n2->fid]->local[n2->lid]->stat='*';
			} 
			if(n2->range.lb>=0)//n2������
			{
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='#')
					func[n1->fid]->local[n1->lid]->stat='+';
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='-')
					func[n1->fid]->local[n1->lid]->stat='*';
			} 
			else if(n2->range.ub<=0)//n2�Ǹ���
			{
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='#')
					func[n1->fid]->local[n1->lid]->stat='-';
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='+')
					func[n1->fid]->local[n1->lid]->stat='*';
			} 
			break;
		}
		case 2:
		{
			Node* n1=dfg.node[node->lid];
			Node* n2=dfg.node[node->vid];
			Node* next=dfg.node[node->flow[0]->next];
			if(rev)//���ݷ��� 
				if(node->range.lb<next->range.lb || node->range.ub<next->range.ub)
				{
					Range r1=next->range+n2->range;
					if(r1.lb>n1->range.lb) n1->range.lb=r1.lb;
					if(r1.ub<n1->range.ub) n1->range.ub=r1.ub;
					Range r2=n1->range-next->range;
					if(r2.lb>n2->range.lb) n2->range.lb=r2.lb;
					if(r2.ub<n2->range.ub) n2->range.ub=r2.ub;
				}
			node->range=n1->range-n2->range;
			if(n2->range.lb>=0)//n2������
			{
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='#')
					func[n1->fid]->local[n1->lid]->stat='-';
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='+')
					func[n1->fid]->local[n1->lid]->stat='*';
			} 
			else if(n2->range.ub<=0)//n2�Ǹ���
			{
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='#')
					func[n1->fid]->local[n1->lid]->stat='+';
				if(n1->lid>=0 && func[n1->fid]->local[n1->lid]->stat=='-')
					func[n1->fid]->local[n1->lid]->stat='*';
			} 
			break;
		}
		case 3:
		{
			Node* n1=dfg.node[node->lid];
			Node* n2=dfg.node[node->vid];			
			node->range=n1->range*n2->range;
			break;
		}
		case 4:
		{
			Node* n1=dfg.node[node->lid];
			Node* n2=dfg.node[node->vid];
			if(env->vari[n1->vid]->type && env->vari[n2->vid]->type)
				node->range=n1->range/n2->range;
			else node->range=n1->range%n2->range;
			break;
		}
		case 5:
		{
			if(node->range.lb!=-inf) node->range.lb=(int)(float) node->range.lb;
			if(node->range.lb!=-inf) node->range.ub=(int)(float) node->range.ub;
			break;
		}
		case 6:
		{
			node->range.lb=(float) node->range.lb;
			node->range.ub=(float) node->range.ub;
			break;
		}
		case 8:
		{
			Node* n1=dfg.node[node->lid];
			Node* n2=dfg.node[node->vid];
			node->range.lb=min(n1->range.lb,n2->range.lb);
			node->range.ub=max(n1->range.ub,n2->range.ub);
			switch(func[n1->fid]->local[n1->lid]->stat)
			{				
				case '+'://���������ı��� 
				{
					if(node->range.lb==-inf)
						node->range.lb=max(n1->range.lb,n2->range.lb);
					break;
				}
				case '-'://�����ݼ��ı��� 
				{
					if(node->range.ub==inf)
						node->range.ub=min(n1->range.ub,n2->range.ub);
					break;
				}
			}		
			if(node->cid==1) node->range=n2->range;
			if(node->cid==-1) node->range=n1->range;	
			break;
		}
	}
	for(vector<Flow*>::iterator it=node->flow.begin();it!=node->flow.end();it++)
	{//�����ݷ�Χ������һ�ڵ� 
		if(!(*it)->ctrl) dfg.node[(*it)->next]->range=node->range;
		else
		{
			double lb,ub;
			if((*it)->lower==-2) lb=-inf;
			else
			{
				lb=dfg.node[(*it)->lower]->range.lb;
				if((*it)->strict) lb=floor(lb+1);
			}
			if((*it)->upper==-1) ub=inf;
			else
			{
				ub=dfg.node[(*it)->upper]->range.ub;
				if((*it)->strict) ub=ceil(ub-1);
			}
			dfg.node[(*it)->next]->range.lb=max(node->range.lb,lb);
			dfg.node[(*it)->next]->range.ub=min(node->range.ub,ub);
		}
		dfg.node[(*it)->next]->range.lb=max(dfg.node[(*it)->next]->range.lb,dfg.node[(*it)->next]->lb);
		dfg.node[(*it)->next]->range.ub=min(dfg.node[(*it)->next]->range.ub,dfg.node[(*it)->next]->ub);
		if(!dfg.node[(*it)->next]->visit) flow_data(dfg.node[(*it)->next],rev);
	}
}

void ring_check()//��������ͼ�еĻ�
{
	for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
	{
		if((*it)->id==20)
			int test=1+2;
		for(vector<Flow*>::iterator t=(*it)->flow.begin();t!=(*it)->flow.end();t++)
			if((*it)->flow.size()>1 && (*t)->next == (*it)->id && (*t)->ctrl)//��
			{
				if((*t)->upper!=-1)
				{
					(*it)->range.lb++;
					(*it)->range.ub++;
				}
				if((*t)->lower!=-2)
				{
					(*it)->range.lb--;
					(*it)->range.ub--;
				}
			} 
	}
} 

void analyze(int fid)//��������(��������idΪfid)�ķ���ֵ��Χ 
{
	btag = new bool[func[fid]->basic.size()];
	build_data_flow(func[fid]);
	for(vector<Node*>::iterator it=dfg.node.begin();it!=dfg.node.end();it++)
	{//��ʼ��������Χ 
		for(int i=0;i<param_range.size();i++)
			if(((*it)->op==0 || (*it)->op==5 || (*it)->op==6) &&
					(*it)->vid==env->local[i]->pos && (*it)->fid==env->id)
			{
				(*it)->range=param_range[i];
				start.push_back(*it);
			}
	}	
	bool rev=0; 
	for(int i=0;i<5;i++)
	{						
		dfg.clear_tag();
		for(vector<Node*>::iterator it=start.begin();it!=start.end();it++)
			if(!(*it)->visit) flow_data(*it,rev);
		if(i==2) constrain(env);	
		if(i==3) ring_check();
		if(i==3) phi_check();							 
		if(i==3) rev=1;						
	} 
	print_dfg();
}

Range run(int fid); 
Range* execute(Sent* sent, Func* env)//����ִ�� 
{
	switch(sent->op)
	{
		case 0://��ֵ 
		{
			Vari* v=env->vari[sent->left_value];
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				v->range.lb=v->range.ub=t;				
			}
			else
			{
				int t=atoi((sent->arg2).data());
				Vari* v2=env->vari[t];
				v->range.lb=v2->range.lb;
				v->range.ub=v2->range.ub;
			}
			return NULL;
		}
		case 1://�ӷ� 
		{
			Vari* v=env->vari[sent->left_value];
			Vari* v1;
			Vari* v2;
			if(sent->arg1[0]=='$')
			{
				double t=atof((sent->arg1).substr(1,(sent->arg1).length()-1).data());
				v1=new Vari(-1,v->type,"const");
				v1->range.lb=v1->range.ub=t;	
			}
			else v1=env->vari[atoi((sent->arg1).data())];
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				v2=new Vari(-1,v->type,"const");
				v2->range.lb=v2->range.ub=t;	
			}
			else v2=env->vari[atoi((sent->arg2).data())];
			v->range=v1->range+v2->range;
			if(sent->arg1[0]=='$') delete v1;
			if(sent->arg2[0]=='$') delete v2;
			return NULL;
		}
		case 2://���� 
		{
			Vari* v=env->vari[sent->left_value];
			Vari* v1;
			Vari* v2;
			if(sent->arg1[0]=='$')
			{
				double t=atof((sent->arg1).substr(1,(sent->arg1).length()-1).data());
				v1=new Vari(-1,v->type,"const");
				v1->range.lb=v1->range.ub=t;	
			}
			else v1=env->vari[atoi((sent->arg1).data())];
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				v2=new Vari(-1,v->type,"const");
				v2->range.lb=v2->range.ub=t;	
			}
			else v2=env->vari[atoi((sent->arg2).data())];
			v->range=v1->range-v2->range;
			if(sent->arg1[0]=='$') delete v1;
			if(sent->arg2[0]=='$') delete v2;
			return NULL;
		}
		case 3://�˷� 
		{
			Vari* v=env->vari[sent->left_value];
			Vari* v1;
			Vari* v2;
			if(sent->arg1[0]=='$')
			{
				double t=atof((sent->arg1).substr(1,(sent->arg1).length()-1).data());
				v1=new Vari(-1,v->type,"const");
				v1->range.lb=v1->range.ub=t;	
			}
			else v1=env->vari[atoi((sent->arg1).data())];
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				v2=new Vari(-1,v->type,"const");
				v2->range.lb=v2->range.ub=t;	
			}
			else v2=env->vari[atoi((sent->arg2).data())];
			v->range=v1->range*v2->range;
			if(sent->arg1[0]=='$') delete v1;
			if(sent->arg2[0]=='$') delete v2;
			return NULL;
		}
		case 4://����
		{
			Vari* v=env->vari[sent->left_value];
			Vari* v1;
			Vari* v2;
			if(sent->arg1[0]=='$')
			{
				double t=atof((sent->arg1).substr(1,(sent->arg1).length()-1).data());
				v1=new Vari(-1,v->type,"const");
				v1->range.lb=v1->range.ub=t;	
			}
			else v1=env->vari[atoi((sent->arg1).data())];
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				v2=new Vari(-1,v->type,"const");
				v2->range.lb=v2->range.ub=t;	
			}
			else v2=env->vari[atoi((sent->arg2).data())];
			if(v->type) v->range=v1->range/v2->range;
			else v->range=v1->range%v2->range;
			if(sent->arg1[0]=='$') delete v1;
			if(sent->arg2[0]=='$') delete v2;
			return NULL;
		}
		case 5://����ǿ��ת�� 
		{
			Vari* v=env->vari[sent->left_value];
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				v->range.lb=v->range.ub=t;				
			}
			else
			{
				int t=atoi((sent->arg2).data());
				Vari* v2=env->vari[t];
				v->range.lb=(int) v2->range.lb;
				v->range.ub=(int) v2->range.ub;
			}
			return NULL;
		}
		case 6://����ǿ��ת�� 
		{
			Vari* v=env->vari[sent->left_value];
			if(sent->arg2[0]=='$')
			{
				double t=atof((sent->arg2).substr(1,(sent->arg2).length()-1).data());
				v->range.lb=v->range.ub=t;				
			}
			else
			{
				int t=atoi((sent->arg2).data());
				Vari* v2=env->vari[t];
				v->range.lb=(float) v2->range.lb;
				v->range.ub=(float) v2->range.ub;
			}
			return NULL;
		}
		case 7://�������� 
		{
			Vari* v=env->vari[sent->left_value];
			int fid;
			for(int i=0;i<func.size();i++)//�ҵ������ú��� 
				if(func[i]->name == sent->arg1)
				{
					fid=i;
					break;
				}
			string args=sent->arg2;
			int c=0;
			int pos=0;
			while(1)
			{
				int i=pos;
				if(i>=args.length()) break;
				for(;args[i]!=';';i++);
				string arg=args.substr(pos,i-pos);
				if(arg[0]=='$')//������� 
				{
					double t=atof(arg.substr(1,arg.length()-1).data());
					func[fid]->vari[func[fid]->local[c]->pos]->range.lb=t;
					func[fid]->vari[func[fid]->local[c]->pos]->range.ub=t;		
				}
				else
				{
					Vari* v1=env->vari[atoi(arg.data())];
					func[fid]->vari[func[fid]->local[c]->pos]->range.lb=v1->range.lb;
					func[fid]->vari[func[fid]->local[c]->pos]->range.ub=v1->range.ub;
				}
				c++;
				pos=i+1;
			}
			int old_bb=G_bb;
			v->range=run(fid);
			G_bb=old_bb;
			return NULL;
		} 
		case 8://phi����
		{
			Vari* v=env->vari[sent->left_value];
			int pos=0,i;
			for(i=pos;sent->arg1[i]!=';';i++);
			Vari* v1=env->vari[atoi((sent->arg1).substr(pos,i-pos).data())];
			pos=i+1;
			for(i=pos;sent->arg1[i]!=';';i++);
			int from1=atoi((sent->arg1).substr(pos,i-pos).data());
			pos=0;
			for(i=pos;sent->arg2[i]!=';';i++);
			Vari* v2=env->vari[atoi((sent->arg2).substr(pos,i-pos).data())];
			if(G_from == from1)
			{
				v->range.lb=v1->range.lb;
				v->range.ub=v1->range.ub;
			}
			else
			{
				v->range.lb=v2->range.lb;
				v->range.ub=v2->range.ub;
			}
			return NULL;
		} 
		case 9://return
		{
			Vari* v=env->vari[sent->left_value];
			return &(v->range);
		}
	}
}

bool judge(Cond* cond, Func* env)//�ж��Ƿ�������� 
{
	Vari* v1;
	Vari* v2;
	if(cond->arg1[0]=='$')
	{
		double t=atof((cond->arg1).substr(1,(cond->arg1).length()-1).data());
		v1=new Vari(-1,1,"const");
		v1->range.lb=v1->range.ub=t;	
	}
	else v1=env->vari[atoi((cond->arg1).data())];
	if(cond->arg2[0]=='$')
	{
		double t=atof((cond->arg2).substr(1,(cond->arg2).length()-1).data());
		v2=new Vari(-1,1,"const");
		v2->range.lb=v2->range.ub=t;	
	}
	else v2=env->vari[atoi((cond->arg2).data())];
	bool b=0;
	switch(cond->op)
	{
		case 1://==
		{
			b=(v1->range.lb==v2->range.lb && v1->range.ub==v2->range.ub);
			break;
		}
		case 2://>
		{
			b=v1->range.lb>v2->range.ub;
			break;
		}
		case 3://<
		{
			b=v1->range.ub<v2->range.lb;
			break;
		}
		case -1://!=
		{
			b=(v1->range.lb!=v2->range.lb || v1->range.ub!=v2->range.ub);
			break;
		}
		case -2://<=
		{
			b=v1->range.ub<=v2->range.lb;
			break;
		}
		case -3://>=
		{
			b=v1->range.lb>=v2->range.ub;
			break;
		}
	}	
	if(cond->arg1[0]=='$') delete v1;
	if(cond->arg2[0]=='$') delete v2;
	return b;
}

int go_where(Basic* basic, Func* env)//�ж���һ��Ӧ��ȥ�ĸ������� 
{
	if(judge(basic->if_edge->cond,env)) return basic->if_edge->t;
	if(judge(basic->else_edge->cond,env)) return basic->else_edge->t;
}

Range run(int fid)//�ܴ��� 
{
	Range r;
	G_bb=1;
	while(G_bb!=0)//����exit������ʱ���� 
	{
		for(vector<Sent*>::iterator it=func[fid]->basic[G_bb]->sent.begin();
				it!=func[fid]->basic[G_bb]->sent.end();it++)//ִ��ÿһ����� 
		{
			Range* p;
			if((p=execute((*it),func[fid])) != NULL)//���ִ�е�return��� 
				r=*p; 
		}
		G_from=G_bb;
		if(func[fid]->basic[G_bb]->if_edge == NULL) //�ҵ���һ�������� 
			G_bb=func[fid]->basic[G_bb]->exit[0];
		else G_bb=go_where(func[fid]->basic[G_bb],func[fid]);
	}
	return r;
}

int main()
{
	string s;
	ifstream fin;
	fin.open("0.txt");//������Χ�ļ� 
	string plb,pub;
	while(fin>>plb>>pub)
	{
		Range r;
		if(plb=="-inf") r.lb=-inf;
		else r.lb=atof(plb.data());
		if(pub=="inf" || pub=="+inf") r.ub=inf;
		else r.ub=atof(pub.data());
		param_range.push_back(r);
	}
	fin.close();
	fin.open("t1.ssa");//ssa�ļ� 
	while(getline(fin,s))
	{
		if(s.length()==0) continue;
		if(s[0]==';' || s[0]=='{' || s[0]=='}') continue;
		remove_space(s);//ȥ�����ǰ�ÿո� 
		if(s.length()>1 && s[0]=='i' && s[1]=='f')//�ϲ�if-else���Ϊһ�� 
			for(int i=0;i<3;i++)
			{
				string s1;
				getline(fin,s1);
				remove_space(s1);
				s=s+' '+s1;
			}
		cout<<"origin sentence: "<<s<<'\n';
		parse(s);
	}		
	fin.close();
	if(param_range.size()==0)
	{
		Range range=run(G_fcount-1);
		cout<<'['<<range.lb<<','<<range.ub<<']';
	} 
	else
	{
		analyze(G_fcount-1);
		cout<<'['<<ret->range.lb<<','<<ret->range.ub<<']';
	}	
	return 0;
}
