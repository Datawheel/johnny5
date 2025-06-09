import json, os, operator, copy, mwparserfromhell, datetime as dt, codecs, re, warnings
from collections import defaultdict
from multiprocessing import cpu_count

import nltk.data,nltk
from nltk.stem import WordNetLemmatizer
nltk.download('wordnet', quiet=True)
nltk.download('punkt', quiet=True)
nltk.download('averaged_perceptron_tagger', quiet=True)

from dateutil.relativedelta import relativedelta
from pandas import DataFrame, read_csv, concat, merge
from numpy import mean, array, exp, log, std, minimum
import numpy as np

from scipy.stats import entropy
try:
	import cPickle as pickle
except:
	import pickle
try:
	import spotipy
except:
	warnings.warn('Warning: spotipy module not found')

from .functions import country, _dms2dd, _dt2str, _all_dates
from .query import wd_q, wp_q, _string, _isnum, _rget, get_soup
from .parse_functions import (
	drop_comments, find_nth, parse_date,get_links, correct_titles, parse_ints,
	parse_p
)


class Article:
	"""
	This is the main class for this module.
	All other classes belong to this class.
	The class can be initialized by a en_curid, a title, or a wikidata_id.
	If you want to initialize an empty object, pass it ' '.

	Parameters
	----------
	I : str or int
		Either the english curid, the wikidata id, or the title for the english Wikipedia.
	Itype : str (optional)
		Either 'title', 'curid', or 'wdid'
		Type of I.
	"""
	def __init__(self, I, Itype=None, slow_connection=False):
		Itype = _id_type(I) if Itype is None else Itype
		if Itype == 'title':
			I = 'NA' if I.strip() =='' else I
		if Itype not in ['title','curid','wdid']:
			raise NameError("Unrecognized Itype, please choose between title, curid, or wdid")
		self.I = {'title': None, 'curid': None, 'wdid': None}
		if Itype == 'title' or Itype == 'wdid':
			self.I[Itype] = I.strip()
		else:
			self.I[Itype] = I

		self._data = {'wp': None, 'wd': None}
		self._curid_nonen = None

		self._slow_connection = slow_connection

		self._extracts = {'en': None}

		self._langlinks_dat = None
		self._langlinks = None

		self._infobox = None
		self.raw_box  = None

		self._image_url = None

		self._wd_claims      = {}
		self._wd_claims_data = {}

		self._content = None

		self._creation_date = {}
		self._feats = None
		self._occ   = None

		self.no_wp = False
		self.no_wd = False

		self._revisions = {}
		self._daily_views = {}
		self._previous_titles = None

		self._isa_values = None
		self._tables = None

		self._get_previous = True

		self._views = {'en': DataFrame([], columns=['year', 'month', 'day', 'views'])}

		if not self._slow_connection:
			self.find_article()

	def __repr__(self):
		out = ''
		out+= 'curid : '+str(self.I['curid'])+'\n' if self.I['curid'] is not None else 'curid : \n'
		out+= 'title : '+self.I['title']+'\n' if self.I['title'] is not None else 'title : \n'
		out+= 'wdid  : '+self.I['wdid'] if self.I['wdid'] is not None else 'wdid  : '
		return out

	def __str__(self):
		self.redirect()
		out = ''
		self.title(),self.curid(),self.wdid()
		if not self.no_wp:
			out+= 'curid : '+str(self.curid())+'\n'
			out+= 'title : '+self.title()+'\n'
		else:
			out+= 'curid : None\n'
			out+= 'title : None\n'
		if not self.no_wd:
			out+= 'wdid  : '+self.wdid()+'\n'
		else:
			out+= 'wdid  : None\n'
		out+= 'L     : '+str(self.L())
		return out

	def _missing_wd(self):
		"""This function is used to signal that the article does not correspond
		to a Wikidata page.
		"""
		self.no_wd = True
		self.I['wdid'] = None
		self._data['wd'] = None

	def _missing_wp(self):
		"""This function is used to signal that the article does not correspond
		to a Wikipedia page.
		"""
		self.no_wp = True
		self.I['title'] = None
		self.I['curid'] = None
		self._data['wp'] = None

	def wd_label(self):
		"""Returns the 'label' of the Wikidata entity (the label referes to the
		title).
		"""
		try:
			return self._data['wd']['labels']['en']['value']
		except:
			return None

	def data_wp(self):
		"""Returns the metadata about the Wikipedia page."""
		if self._data['wp'] is None and not self.no_wp:
			if (self.I['curid'] is not None):
				self._data['wp'] = list(wp_q({'prop':'pageprops','ppprop':'wikibase_item','pageids':self.I['curid']})['query']['pages'].values())[0]
			elif (self.I['title'] is not None):
				self._data['wp'] = list(wp_q({'prop':'pageprops','ppprop':'wikibase_item','titles':self.I['title']})['query']['pages'].values())[0]
			elif (self.I['wdid'] is not None):
				if self._data['wd'] is None:
					r = wd_q({'languages':'en','ids':self.I['wdid']})
					if 'error' in list(r.keys()):
						print(r['error']['info'])
						self._missing_wd()
					else:
						self._data['wd'] = list(r['entities'].values())[0]
				if 'sitelinks' in list(self._data['wd'].keys()):
					sitelinks = self._data['wd']['sitelinks']
					if 'enwiki' in list(sitelinks.keys()):
						self.I['title'] = sitelinks['enwiki']["title"]
					elif not self.no_wd:
						self._missing_wp()
				else:
					self._missing_wp()
				if self._data['wp'] is None and self.I['title'] is not None:
					self._data['wp'] = list(wp_q({'prop':'pageprops','ppprop':'wikibase_item','titles':self.I['title']})['query']['pages'].values())[0]
			else:
				raise NameError('No identifier found.')
			if not self.no_wp:
				if ('missing' in list(self._data['wp'].keys()))|('invalid' in list(self._data['wp'].keys())):
					self._missing_wp()
		return self._data['wp']

	def data_wd(self):
		"""Returns the metadata about the Wikidata page."""
		if self._data['wd'] is None and not self.no_wd:
			if self.I['wdid'] is None:
				d = self.data_wp()
				d = self._data['wp']
				if 'wikibase_item' in list(d['pageprops'].keys()):
					self.I['wdid'] = d['pageprops'][u'wikibase_item']
				else:
					self._missing_wd()
			if self._data['wd'] is None:
				self._data['wd'] = list(wd_q({'languages':'en','ids':self.I['wdid']})['entities'].values())[0]
		return self._data['wd']

	def wdid(self):
		"""Returns the wdid of the article.
		Will get it if it is not provided.
		"""
		if self.I['wdid'] is None and not self.no_wd:
			d = self.data_wp()
			if 'pageprops' in d:
				d = self.data_wp()['pageprops']
				if 'wikibase_item' in list(d.keys()):
					self.I['wdid']  = d['wikibase_item']
				else:
					self._missing_wd()
			else:
				self._missing_wd()
		return self.I['wdid']

	def curid(self):
		"""Returns the english curid of the article.
		Will get it if it is not provided.
		"""
		if self.I['curid'] is None and not self.no_wp:
			if self.data_wp() is not None:
				self.I['curid'] = self.data_wp()['pageid']
		return self.I['curid']

	def title(self):
		"""Returns the title of the article.
		Will get it if it is not provided.
		"""
		if self.I['title'] is None and not self.no_wp:
			if self.data_wp() is not None:
				self.I['title'] = self.data_wp()['title']
		return self.I['title']

	def url(self, wiki='wp', lang='en'):
		if wiki == 'wp':
			if self.title() is None:
				raise NameError("No Wikipedia page corresponding to this article")
			elif lang == 'en':
				url = 'https://en.wikipedia.org/wiki/' + self.title().replace(' ', '_')
				return url
			else:
				if lang in list(self.langlinks().keys()):
					url = 'https://'+lang+'.wikipedia.org/wiki/' + self.langlinks(lang).replace(' ', '_')
					print(url)
					return url
				else:
					raise NameError('No article in this edition')
		elif wiki == 'wd':
			if self.no_wd:
				raise NameError("No Wikidata page corresponding to this article")
			url = 'https://www.wikidata.org/wiki/'+self.wdid()
			return url
		else:
			raise NameError('Wrong wiki')

	def curid_nonen(self, nonen=True):
		"""
		Gets the curid in a non-english language.
		The curid is a string and has the form: 'lang.curid'

		Parameters
		----------
		nonen : boolean (True)
			If False, and if the page exists in english, it will return the english curid.
		"""
		if self._curid_nonen is None:
			for lang,title in list(self.langlinks().items()):
				try:
					r = list(wp_q({'prop':'pageprops','ppprop':'wikibase_item','titles':title},lang=lang)['query']['pages'].values())[0]
					self._curid_nonen = lang+'.'+str(r['pageid'])
					break
				except:
					pass
		if nonen|(self.curid() is None):
			return self._curid_nonen
		else:
			return self.curid()

	def wiki_links(self,section_title=None):
		'''
		Gets all the Wikipedia pages linked from the article.
		It only returns Wikipedia pages.

		Returns
		-------
		titles : set
			Set of titles for the Wikipedia pages linked from the article.
		'''
		if 'category:' not in self.title().lower():
			remove = set(['##'])
			if section_title is None:
				links = mwparserfromhell.parse(self.content()).filter_wikilinks()
			else:
				links = mwparserfromhell.parse(self.section(section_title)).filter_wikilinks()
			titles = set([link.encode('utf-8').split('|')[0].replace('[[','').replace(']]','').strip() for link in links])
			titles = titles.difference(remove)
		else:
			titles = set([])
			soup = get_soup(self.title())
			lists = soup.find_all(name='div',attrs={'id':'mw-pages'})
			for l in lists:
				for link in l.find_all(name='a'):
					if link.contents[0] != 'learn more':
						titles.add(link['href'].replace('/wiki/',''))
		return titles

	def html_soup(self):
		'''
		Gets the html for the English Wikipedia page parsed as a BeautifulSoup object.
		'''
		soup = get_soup(self.title())
		return soup

	def tables(self, i=None):
		'''
		Gets tables in the page.

		Parameters
		----------
		i : int (optional)
			Position of the table to get.
			If not provided it will return a list of tables

		Returns
		-------
		tables : list or pandas.DataFrame
			The parsed tables found in the page.
		'''
		if self._tables is None:
			self._tables = []
			soup = get_soup(self.title())
			for table in soup.find_all(name='table'):
				head = [h.contents[0] for h in table.find_all(name='th')]
				out = []
				for line in table.find_all(name='tr'):
					line = line.find_all(name='td')
					if len(line)!=0:
						out.append(tuple(line))
				self._tables.append(DataFrame(out,columns=head))
		if i is not None:
			return self._tables[i]
		else:
			return self._tables

	def infobox(self,lang='en',force=False):
		"""Returns the infobox of the article.

		Parameters
		----------
		lang : str (default='en')
			Language edition to get the infobox from.
		force : boolean (False)
			If True it will 'force' the search for the infobox by getting the template that is the most similar to an Infobox.
			Recommended usage is only for non english editions.
		"""
		if self._infobox is None and lang == 'en' and not self.no_wp:
			if self.raw_box is None:
				rbox = '#redirect'
				while '#redirect' in rbox.lower():
					r = wp_q({'prop':"revisions",'rvprop':'content','rvsection':0,'pageids':self.curid()})
					try:
						rbox = list(r['query']['pages'].values())[0]['revisions'][0]['*']
					except:
						rbox = ''
					if '#redirect' in rbox.lower():
						title = rbox.split('[[')[-1].split(']]')[0].strip()
						self.__init__(title,Itype='title')
				self.raw_box = rbox
			wikicode = mwparserfromhell.parse(self.raw_box)
			templates = wikicode.filter_templates()
			box = {}
			box_pos = 0
			for template in templates:
				name = template.name.strip().lower()
				if 'infobox' in name:
					box_ = {}
					box_type = drop_comments(_string(name).replace('infobox','')).strip()
					for param in template.params:
						key = drop_comments(_string(param.name.strip_code())).strip().lower()
						value = _string(param.value).strip()

						box_[key] = value
					box_['box_pos'] = box_pos
					box_pos+=1
					box[box_type] = box_
			if box is None:
				self._infobox = {}
			else:
				self._infobox = box
		return self._infobox if lang == 'en' else self._infobox_nonen(lang,force=force)

	def _infobox_nonen(self,lang,force=False):
		'''Gets the infobox for non english wikipedias.'''
		ibox_codebook = defaultdict(lambda:'infobox', {'es':'ficha de','ca':'infotaula de','sv':'infobox',
														'nl':'infobox','fr':'infobox','pl':'infobox','pt':'info',
														'ru':u'\u0433\u043e\u0441\u0443\u0434\u0430\u0440\u0441\u0442\u0432\u0435\u043d\u043d\u044b\u0439'
														})
		self.redirect()
		if lang not in list(self.langlinks().keys()):
			return {}
		r = wp_q({'prop':"revisions",'rvprop':'content','rvsection':0,'titles':self.langlinks(lang)},lang=lang)
		try:
			rbox = list(r['query']['pages'].values())[0]['revisions'][0]['*']
		except:
			rbox = ''
		ibox_name = ibox_codebook[lang]
		wikicode = mwparserfromhell.parse(rbox)
		templates = wikicode.filter_templates()
		box = {}
		box_pos = 0
		lengths = []
		for template in templates:
			name = template.name.strip().lower()
			lengths.append(len(template.params))
			if ibox_name in name:
				box_ = {}
				box_type = drop_comments(_string(name).replace(ibox_name,'')).strip()
				for param in template.params:
					key = drop_comments(_string(param.name.strip_code())).strip().lower()
					value = _string(param.value).strip()
					box_[key] = value
				box_['box_pos'] = box_pos
				box_pos+=1
				box[box_type] = box_

		if box == {} and force:
			lengths.append(7) #Infobox should have at least 7 fields
			length = max(lengths)
			for template in templates:
				name = template.name.strip().lower()
				if len(template.params) >= length:
					box_ = {}
					box_type = drop_comments(_string(name)).strip()
					for param in template.params:
						key = drop_comments(_string(param.name.strip_code())).strip().lower()
						value = _string(param.value).strip()
						box_[key] = value
					box_['box_pos'] = box_pos
					box_pos+=1
					box[box_type] = box_

		return box

	def extract(self,lang='en'):
		'''
		Returns the page extract (brief description).

		Parameters
		----------
		lang : str (default='en')
			Language edition to get the infobox from.

		Returns
		-------
		extract : str
			Wikipedia page extract.
		'''
		if lang=='en':
			if self._extracts['en'] is None:
				r = wp_q({'prop':'extracts','exintro':'','explaintext':'','pageids':self.curid()})
				self._extracts['en'] = list(r['query']['pages'].values())[0]['extract']
			return self._extracts['en']
		else:
			if lang not in self._extracts.keys():
				title = self.langlinks(lang)
				if title !='NULL':
					r = wp_q({'prop':'extracts','exintro':'','explaintext':'','titles':title},lang=lang)
					self._extracts[lang] = list(r['query']['pages'].values())[0]['extract']
				else:
					self._extracts[lang] = 'NULL'
			return self._extracts[lang]

	def langlinks(self,lang=None):
		"""Returns the langlinks of the article.

		Parameters
		----------
		lang : str (optional)
			Language to get the link for.

		Returns
		-------
		out : str or dict
			If a language is provided, it will return the name of the page in that language.
			If no language is provided, it will resturn a dictionary with the languages as keys and the titles as values.
		"""
		if lang is not None:
			if lang =='en':
				return self.title()
		if self._langlinks is None:
			if self._langlinks_dat is None:
				for Itype in ['curid','title','wdid']:
					if self.I[Itype] is not None:
						if Itype == 'wdid':
							if 'sitelinks' in list(self.data_wd().keys()):
								sitelinks = self.data_wd()[u'sitelinks']
								self._langlinks_dat = []
								for lan in sitelinks:
									lan = lan.strip().lower()
									if lan[-4:] == 'wiki' and lan != 'commonswiki':
										val = {'lang':lan[:-4],'*':sitelinks[lan]['title']}
										self._langlinks_dat.append(val)
							else:
								self._langlinks_dat = []
						else:
							if Itype == 'curid':
								r = wp_q({'prop':'langlinks','lllimit':500,'pageids':self.I[Itype]})
							elif Itype == 'title':
								r = wp_q({'prop':'langlinks','lllimit':500,'titles':self.I[Itype]})
							if 'langlinks' in list(list(r['query']['pages'].values())[0].keys()):
								self._langlinks_dat = list(r['query']['pages'].values())[0]['langlinks']
							else:
								self._langlinks_dat = []
						break
			self._langlinks = {val['lang']:val['*'] for val in self._langlinks_dat}
			if 'en' not in list(self._langlinks.keys()) and self.title() is not None:
				self._langlinks['en'] = self.title()
		l = defaultdict(lambda:'NULL',self._langlinks)
		return self._langlinks if lang is None else l[lang]

	def creation_date(self,lang=None):
		'''
		Gets the creation date of the different Wikipedia language editions.
		The Wikipedia API requires this data to be requestes one page at a time, so there is no boost in collecting pages into a list.

		Parameters
		----------
		lang : str (optional)
			Language to get the creation date for.

		Returns
		-------
		timestamp : str or dict
			Timestamp in the format '2002-07-26T04:32:17Z'.
			If lang is not provided it will return a dictionary with languages as keys and timestamps as values.
		'''
		if lang is None:
			for lang in self.langlinks():
				if lang not in list(self._creation_date.keys()):
					title = self.langlinks(lang=lang)
					r = wp_q({'prop':'revisions','titles':title,'rvlimit':1,'rvdir':'newer'},lang=lang,continue_override=True)
					try:
						timestamp = list(r['query']['pages'].values())[0]['revisions'][0]['timestamp']
					except:
						timestamp = 'NA'
					self._creation_date[lang] = timestamp
			return self._creation_date
		else:
			if lang not in list(self.langlinks().keys()):
				raise NameError('No edition for language: '+lang)
			if (lang not in list(self._creation_date.keys())):
				title = self.langlinks(lang=lang)
				r = wp_q({'prop':'revisions','titles':title,'rvlimit':1,'rvdir':'newer'},lang=lang,continue_override=True)
				try:
					timestamp = list(r['query']['pages'].values())[0]['revisions'][0]['timestamp']
				except:
					timestamp = 'NA'
				self._creation_date[lang] = timestamp
			return self._creation_date[lang]

	def L(self):
		"""Returns the number of language editions of the article.

		Returns
		-------
		L : int
			Number of Wikipedia language editions this article exists in.
		"""
		return len(self.langlinks())

	def CumulativePageviews(self, windowDays=180):
		"""Gets the accumulated pageviews for all languages until today, starting
		from the given time window in days. It will only consider editions that
		were created windowDays before today.

		Parameters
		----------
		windowDays : int (optional)
			Default is 180 days. This parameter indicates the start date for the pageviews.

		Returns
		-------
		PV : list
			List of accumulated pageviews in non-english languages.
		PVen : float
			Accumulated pageviews in english.
		"""
		PV = []
		today = dt.datetime.now()
		time_window = dt.timedelta(days=windowDays)
		start_date = today - time_window
		start_date_str = str(start_date.year)+'-'+('0'+str(start_date.month))[-2:]

		for lang in self.langlinks().keys():
			if lang != 'en':
				try:
					cdate = dt.datetime.strptime(self.creation_date(lang).split('T')[0], '%Y-%m-%d')
				except:
					continue

				if (today - cdate) > time_window:
					try:
						views = self.pageviews(start_date_str, lang=lang)['views'].sum()
						PV.append(views)
					except:
						pass

		if 'en' in self.langlinks().keys():
			try:
				PVen = self.pageviews(start_date_str, lang='en')['views'].sum()
			except:
				PVen = 0
		else:
			PVen = 0

		return PV, PVen

	def previous_titles(self):
		'''
		Gets all the previous titles the page had.
		ONLY WORKS FOR ENGLISH FOR NOW

		Returns
		-------
		titles : set
			Collection of previous titles
		'''
		if self._previous_titles is None:
			r = wp_q({'prop':'revisions','pageids':self.curid(),'rvprop':["timestamp",'user','comment'],'rvlimit':'500'})
			titles = set([])
			for rev in list(r['query']['pages'].values())[0]['revisions']:
				if 'comment' in list(rev.keys()):
					if 'moved page' in rev['comment']:
						comment = rev['comment']
						titles.add(comment[comment.find('[[')+2:].split(']]')[0])
			self._previous_titles = titles
		return self._previous_titles

	def image_url(self):
		'''
		Gets the url for the image that appears in the infobox.
		It iterates over a list of languages, ordered according to their wikipedia size, until it finds one.

		Returns
		-------
		img_url : str
			Ful url for the image.
		'''
		self.data_wp()
		if self._image_url is None:
			if not self.no_wp:
				for lang in ['en','sv','ceb','de','nl','fr','ru','it','es','war','pl','vi','ja','pt','zh','uk','ca','fa','no','ar','sh','fi']:
					results = self._image_url_lang(lang)
					if len(results) != 0:
						self._image_url = results[0]
						break
			elif not self.no_wd:
				try:
					images = 'File:'+self.wd_prop('P18')[0]['value'].replace(' ','_')
					r = wp_q({'titles':images,'prop':'imageinfo','iiprop':'url','iilimit':1},continue_override=True)
					self._image_url = list(r['query']['pages'].values())[0]['imageinfo'][0]['url']
				except:
					pass
			if self._image_url is None:
				self._image_url = 'NULL'
		return self._image_url

	def _image_url_lang(self,lang):
		tags_codebook = defaultdict(
						lambda:['image','img','image_name'],
							{'en':['image','image_name','img','smallimage'],'es':['imagen','img'],
							'pt':['imagem','img'],'nl':['afbeelding'],'fr':['image'],'ja':[u'\u753b\u50cf'],
							'ru':[u'\u0438\u0437\u043e\u0431\u0440\u0430\u0436\u0435\u043d\u0438\u0435'],
							'uk':[u'\u0437\u043e\u0431\u0440\u0430\u0436\u0435\u043d\u043d\u044f'],
							'pl':[u'zdj\u0119cie'],'sv':['bild','img']
							})
		images = []
		tags = tags_codebook[lang]
		ibox = self.infobox(lang=lang,force=True)
		for btype in ibox:
			box = ibox[btype]
			box_pos = box['box_pos']
			if box_pos==0:
				for tag in tags:
					if tag in list(box.keys()):
						images.append(box[tag].strip())
		for btype in ibox:
			box = ibox[btype]
			box_pos = box['box_pos']
			if box_pos==1:
				for tag in tags:
					if tag in list(box.keys()):
						images.append(box[tag].strip())
		imgs = []
		for image in images:
			if image.strip() != '':
				if '[[' in image:
					image = image[image.find('[[')+2:].split(']]')[0].split('|')[0]
				if image.lower()[:5] != 'file:' and image.lower()[:6] != 'image:':
					imgs.append('Image:' + image)
				else:
					imgs.append(image)
		images = imgs
		if len(images)!=0:
			try:
				r = wp_q({'titles':images,'prop':'imageinfo','iiprop':'url','iilimit':1},continue_override=True)
				norm = {}
				if 'normalized' in list(r['query'].keys()): #This is to keep the order
					norm = {val['from']:val['to'] for val in r['query']['normalized']}
				pages = {}
				for val in list(r['query']['pages'].values()):
					try:
						pages[val['title']] = val['imageinfo'][0]['url']
					except:
						pass
				results = []
				for image in images:
					if image in list(norm.keys()):
						image = norm[image]
					results.append(pages[image])
			except:
				results = []
		else:
			results = []
		return results

	def wd_prop(self,prop):
		'''
		Gets the requested Wikidata propery.

		Parameters
		----------
		prop : str
			Wikidata code for the property.

		Returns
		-------
		props : list
			List of values for the given property.

		Examples
		--------
		To get the date of birth of Albert Einstein run:
		>>> b = johnny5.article('Q937')
		>>> b.wd_prop('P569')
		'''
		if prop not in list(self._wd_claims.keys()):
			data = self.data_wd()
			if prop in list(data['claims'].keys()):
				vals = data['claims'][prop]
				try:
					out = []
					for val in vals:
						val = val['mainsnak']['datavalue']['value']
						if isinstance(val,dict):
							out.append(defaultdict(lambda:'NA',val))
						else:
							out.append(defaultdict(lambda:'NA',{'value':val}))
					self._wd_claims[prop] = out
				except:
					self._wd_claims[prop] = [defaultdict(lambda:'NA')]
			else:
				self._wd_claims[prop] = [defaultdict(lambda:'NA')]
		return self._wd_claims[prop]

	def dump(self, path='', file_name=None):
		'''
		Dumps the object to a file.
		'''
		out = self.__dict__
		file_name = path+str(self.curid())+'.json' if file_name is None else path +  file_name
		with open(file_name, 'w') as outfile:
			json.dump(out, outfile)

	def content(self, lang='en'):
		'''
		Returns the content of the Wikipedia page in the selected language.
		The output is in Wikipedia markup.

		Parameters
		----------
		lang : str (default='en')
			Language

		Returns
		-------
		content : str
			Content for the page in the given language.
			Content is in WikiMarkup
		'''
		if lang == 'en':
			if self._content is None and not self.no_wp:
				if self.title() is not None:
					r = wp_q({'titles':self.title(),'prop':'revisions','rvprop':'content'})
					if ('interwiki' in list(r['query'].keys())):
						self._missing_wp()
						return '#REDIRECT [['+r['query']['interwiki'][0]['title'].strip()+']]'
					elif ('missing' in set(list(r['query']['pages'].values())[0].keys()))|('invalidreason' in list(r['query']['pages'].values())[0].keys()):
						self._missing_wp()
					else:
						if not self.no_wp:
							self._content = list(r['query']['pages'].values())[0]['revisions'][0]['*']
		else:
			raise NameError('Functionality not supported yet.')
		return self._content

	def section(self, section_title):
		'''
		Returns the content inside the given section of the English Wikipedia page.

		Parameters
		----------
		section_title : str
			Title of the section.

		Returns
		-------
		content : str
			Content of the section in WikiMarkup
		'''
		title = section_title.strip()
		out = []
		insec = False
		depth = 0
		for line in self.content().split('\n'):
			if insec:
				if line.count('=')==depth:
					break
				else:
					out.append(line)
			if line.replace('=','').strip().lower()==title.lower():
				insec=True
				depth = line.count('=')
				out.append(line)
		return '\n'.join(out)

	def redirect(self):
		'''
		Handles redirects if the page has one.
		'''
		content = self.content()
		if content is not None:
			if '#redirect' in content.lower():
				red = content[content.lower().find('#redirect')+9:].strip()
				red = red.split(']]')[0].split('[[')[1].strip()
				if '|' in red:
					red = red.split('|')[-1].strip()
				if self.no_wp:
					self.I['title'] = red
				else:
					self.__init__(red,Itype='title')

	def revisions(self,user=True,lang='en'):
		'''
		Gets the timestamps for the edit history of the Wikipedia article.

		Parameters
		----------
		user : boolean (True)
			If True it returns the user who made the edit as well as the edit timestamp.
		lang : str ('en')
			Language to get the revisions from
		'''
		if lang not in self._revisions.keys():
			if lang=='en':
				r = wp_q({'prop':'revisions','pageids':self.curid(),'rvprop':["timestamp",'user'],'rvlimit':'500'})
				self._revisions['en'] = [(rev['timestamp'],rev['user']) for rev in list(r['query']['pages'].values())[0]['revisions']]
			elif lang in self.langlinks().keys():
				r = wp_q({'prop':'revisions','titles':self.langlinks(lang),'rvprop':["timestamp",'user'],'rvlimit':'500'},lang=lang)
				self._revisions[lang] = [(rev['timestamp'],rev['user']) for rev in list(r['query']['pages'].values())[0]['revisions']]
			else:
				NameError('The Wikipedia page in '+lang+' does not exist.')
		if user:
			return self._revisions[lang]
		else:
			return [val[0] for val in self._revisions[lang]]

	def pageviews(self,start_date,end_date=None,lang='en',cdate_override=False,daily=False,get_previous=True):
		'''
		Gets the pageviews between the provided dates for the given language editions.
		Unless specified, this function checks whether the english page had any other title, and gets the pageviews accordingly.

		Parameters
		----------
		start_date : str
			Start date in format 'yyyy-mm'.
			If start_date=None is passed, it will get all the pageviews for that edition.
		end_date : str
			End date in format 'yyyy-mm'. If it is not provided it will get pagviews until today.
		lang : str ('en')
			Language edition to get the pageviews for.
			If lang=None is passed, it will get the pageviews for all language editions.
		cdate_override : boolean (False)
			If True it will get the pageviews before the creation date
		daily : boolean (False)
			If True it will return the daily pageviews.
		get_previous : boolean (True)
			If True it will search for all the previous titles of the pages and get the pageviews for them as well.
			Only works for English.

		Returns
		-------
		views : pandas.DataFrame
			Table with columns year,month,(day),views.
		'''
		get_previous=False if lang!='en' else get_previous
		if get_previous:
			if (len(self.previous_titles())==0):
				get_previous=False
		if (lang not in self._views.keys())|(self._get_previous!=get_previous):
			self._views[lang] = DataFrame([],columns=['year','month','day','views'])
		self._get_previous=get_previous

		#Checks start and end dates
		oldest = dt.date(2007,12,1)
		rest_split = dt.date(2015,7,1) #starting from this date, it goes to rest
		if start_date is None:
			if cdate_override:
				start_date=oldest
			else:
				y,m,d=self.creation_date(lang=lang).split('T')[0].split('-')
				cdate = dt.date(int(y),int(m),int(d))
				start_date = max([cdate,oldest])
		else:
			y = int(start_date.split('-')[0])
			m = int(start_date.split('-')[1])
			start_date = dt.date(y,m,1)

		if end_date is None:
			end_date = dt.date.today()
		else:
			y = int(end_date.split('-')[0])
			m = int(end_date.split('-')[1])
			end_date = dt.date(y,m,1)+relativedelta(months=1)-dt.timedelta(days=1)

		if start_date>=end_date:
			raise NameError('Start date must come before the end date.')

		#Finds the missing dates
		if len(self._views[lang]) == 0:
			_start_date,_end_date = start_date,end_date
		else:
			cp = merge(_all_dates(start_date,end_date),self._views[lang],how='left')
			missing_dates = [dt.date(y,m,d) for y,m,d in cp[cp['views'].isnull()][['year','month','day']].values]
			if len(missing_dates)!=0:
				_start_date,_end_date = min(missing_dates),max(missing_dates)
			else:
				_start_date,_end_date = start_date,start_date

		#Gets data for missing dates
		if _end_date>_start_date:
			if _start_date>=rest_split:
				self._pv_rest(_start_date,_end_date,get_previous=get_previous,lang=lang)
			elif _end_date<rest_split:
				self._pv_grok(_start_date,_end_date,get_previous=get_previous,lang=lang)
			else:
				self._pv_rest(rest_split,_end_date,get_previous=get_previous,lang=lang)
				self._pv_grok(_start_date,rest_split-dt.timedelta(days=1),get_previous=get_previous,lang=lang)

		#Selects the specified dates
		_views = self._views[lang]
		out = _views[((_views['year']>start_date.year)|((_views['year']==start_date.year)&(_views['month']>=start_date.month)))&((_views['year']<end_date.year)|((_views['year']==end_date.year)&(_views['month']<=end_date.month)))]
		if daily:
			return out.sort_values(by=['year','month','day'])
		else:
			return out.groupby(['year','month']).sum()[['views']].reset_index().sort_values(by=['year','month'])

	def _pv_rest(self, start_date, end_date, get_previous=False, lang='en'):
		url = 'https://wikimedia.org/api/rest_v1/metrics/pageviews/per-article/'+lang+'.wikipedia/all-access/user/'+self.langlinks(lang=lang)+'/daily/'+_dt2str(start_date)+'/'+_dt2str(end_date)
		r = _rget(url) #.json()
		days = _all_dates(start_date,end_date)
		new_views = DataFrame(
			[(int(val['timestamp'][:4]),int(val['timestamp'][4:6]),int(val['timestamp'][6:8]), val['views']) for val in r['items']],
			columns=['year','month','day','views']
		)
		new_views = merge(days, new_views, how='left').fillna(0)

		if get_previous:
			for title in self.previous_titles():
				url = 'https://wikimedia.org/api/rest_v1/metrics/pageviews/per-article/'+lang+'.wikipedia/all-access/user/'+title+'/daily/'+_dt2str(start_date)+'/'+_dt2str(end_date)
				r = _rget(url) #.json()

				new_views_t = DataFrame(
					[(int(val['timestamp'][:4]), int(val['timestamp'][4:6]), int(val['timestamp'][6:8]), val['views']) for val in r['items']],
					columns=['year','month','day','views_t']
				)
				new_views = merge(new_views,new_views_t,how='outer').fillna(0)
				new_views['views'] = new_views['views']+new_views['views_t']
				new_views = new_views.drop('views_t', 1)

		# 🛠️ Fix: ensure _views[lang] is non-empty before concat
		existing_views = self._views.get(lang, DataFrame())
		if existing_views.empty or existing_views.isna().all().all():
			self._views[lang] = new_views
		else:
			self._views[lang] = concat([existing_views, new_views]).drop_duplicates()

	def _pv_grok(self, start_date, end_date, get_previous=False, lang='en'):
		warnings.warn('Grok API is no longer working, so the earliest starting date for pageviews is 2015-07-01')
		# days = _all_dates(start_date,end_date)
		# for y,m in days[['year','month']].drop_duplicates().values:
		# 	self._views[lang] = self._views[lang][(self._views[lang]['year']!=y)|(self._views[lang]['month']!=m)]
		# 	url = ('http://stats.grok.se/json/'+lang+'/'+str(y)+('00'+str(m))[-2:]+'/'+self.langlinks(lang=lang)).replace(' ','_')
		# 	r = _rget(url).json()
		# 	new_views = merge(days[(days['year']==y)&(days['month']==m)],DataFrame([tuple([int(val) for val in (d.split('-')+[v])]) for d,v in r['daily_views'].items()],columns=['year','month','day','views']),how='left').fillna(0)
		# 	if get_previous:
		# 		for title in self.previous_titles():
		# 			url = ('http://stats.grok.se/json/'+lang+'/'+str(y)+('00'+str(m))[-2:]+'/'+title).replace(' ','_')
		# 			r = _rget(url).json()
		# 			new_views_t = merge(days[(days['year']==y)&(days['month']==m)],DataFrame([tuple([int(val) for val in (d.split('-')+[v])]) for d,v in r['daily_views'].items()],columns=['year','month','day','views_t']),how='left').fillna(0)
		# 			new_views = merge(new_views,new_views_t,how='outer').fillna(0)
		# 			new_views['views'] = new_views['views']+new_views['views_t']
		# 			new_views = new_views.drop('views_t',1)
		# 	self._views[lang] = concat([self._views[lang],new_views]).drop_duplicates()

	def find_article(self):
		'''
		Find the article by trying different combinations of the title's capitalization.
		'''
		self.redirect()
		if self.curid() == 'NA':
			old_title = self.title()
			titles = correct_titles(self.title())
			for title in titles:
				self.__init__(title,Itype='title')
				self.redirect()
				if self.curid() != 'NA':
					break
			if self.curid() == 'NA':
				self.__init__(old_title,Itype='title')

	def _is_a(self,full=False):
		'''
		Gets the phrase after the verb 'to be' in the first paragraph of the extract.

		Parameters
		----------
		full : boolean (False)
			If True it will return a tuple with (phrase,sentence,verb), otherwise it returns only phrase.

		Returns
		-------
		phrase : str
			Phrase after the verb 'to be'.
		sentence : str
			Full sentence that contains the verb 'to be'.
		verb : str
			Verb to be as it appears in the sentence.
		'''
		if self._isa_values is None:
			sent_detector = nltk.data.load('tokenizers/punkt/english.pickle')
			lmt = WordNetLemmatizer()
			ex = self.extract()
			sentences = sent_detector.tokenize(ex)
			found_tobe = False
			phrase = ''
			for sentence in sentences:
				words = nltk.pos_tag(nltk.word_tokenize(sentence))
				for word,tag in words:
					if tag[:2] == 'VB':
						if lmt.lemmatize(word, pos='v') == 'be':
							found_tobe = True
							phrase = sentence[sentence.find(word)+len(word):].strip()
							break
				if found_tobe:
					break
			if found_tobe:
				self._isa_values = (phrase,sentence,word.lower())
			else:
				self._isa_values = ('NA','NA','NA')
		if full:
			return self._isa_values
		else:
			return self._isa_values[0]


class Place(Article):
	""" Places (includes methods to get coordinates). """
	def __init__(self,I,Itype=None):
		super(Place, self).__init__(I,Itype=None)
		self._coords = None
		self._is_city = None
		self._wpcities = None
		self._country = None

	def __str__(self):
		out = super(Place, self).__str__()
		out += '\n'
		out += 'coords: ('+str(self.coords()[0])+','+str(self.coords()[1])+')'
		return out

	def coords(self, wiki='wp'):
		"""
		Get the coordinates either from Wikipedia or Wikidata.

		Parameters
		----------
		wiki : string
			Wiki to use, either 'wd' or 'wp'.
			Default is 'wp'
		"""
		if self._coords is None:
			if wiki == 'wd':
				try:
					coords = self.wd_prop('P625')[0]
					self._coords = (coords['latitude'],coords['longitude'])
				except:
					self._coords = ('NA','NA')
			else:
				wiki = 'en' if wiki == 'wp' else wiki

				try:
					if wiki != 'en':
						r = wp_q({'prop':'coordinates',"titles":self.langlinks(wiki)},lang=wiki)
					else:
						r = wp_q({'prop':'coordinates',"pageids":self.curid()})

					coords = list(r['query']['pages'].values())[0]['coordinates'][0]
					self._coords = (coords['lat'],coords['lon'])
				except:
					wikicode = mwparserfromhell.parse(self.content())
					templates = wikicode.filter_templates()
					lat, lon = ('NA', 'NA')
					names = set([template.name.strip().lower() for template in templates])

					if 'coord' in names:
						for template in templates:
							name = template.name.strip().lower()

							if name == 'coord':
								lat = []
								lon = []
								values = template.params
								dms = False

								for i,val in enumerate(values):
									if (val.name.lower().strip() == 'format')&(val.value.lower().strip()=='dms'):
										dms = True

								if not dms:
									for i,val in enumerate(values):
										lat.append(val)
										if (val.lower() == 'n')|(val.lower() == 's'):
											break
									for val in values[i+1:]:
										lon.append(val)
										if (val.lower() == 'e')|(val.lower() == 'w'):
											break
									lat,lon= (_dms2dd(lat),_dms2dd(lon))
								else:
									lat,lon = (float(str(values[0])),float(str(values[1])))

								break
					else:
						parameters = {'latd': 'NA', 'latns': '', 'longd': 'NA', 'longew': ''}
						for template in templates:
							name = template.name.strip().lower()
							if 'infobox settlement' in name:
								for param in template.params:
									name = param.name.strip().lower()
									for ppp in parameters:
										if name == ppp:
											parameters[ppp] = param.value.strip().lower()
								parameters['latd'] = float(parameters['latd'])
								parameters['longd'] = float(parameters['longd'])
								if parameters['latns'] == 's':
									parameters['latd'] *= -1
								if parameters['latew'] == 'w':
									parameters['longd'] *= -1
								break
						lat, lon = (parameters['latd'], parameters['longd'])

					self._coords = (lat,lon)

		return self._coords

	def country(self, GAPI_KEY=None, name=False):
		'''
		Uses google places API to get the country of the given place.

		Parameters
		----------
		GAPI_KEY : str
			Name of the environment variable that has the API key.
		name : boolean (False)
			If True it returns the name of the country.

		Returns
		-------
		ccode : str
			Country code.
		'''
		if self._country is None:
			ctr, ccode = country(self.coords(), save=False, GAPI_KEY=GAPI_KEY)
			self._country = (ctr, ccode)
		if name:
			return self._country[0]
		else:
			return self._country[1]


class Song(Article):
	'''Class for songs.'''
	def __init__(self,I,Itype=None):
		super(Song, self).__init__(I,Itype=None,slow_connection=True)
		self.slow_connection = False
		self._is_song = None
		self._wpsong  = None
		self._genre   = None

	def disambiguate(self,artist=None,in_place=False):
		'''
		It returns the song that it was able to find within the links of a disambiguation page.

		Parameters
		----------
		artist : str (optional)
			If provided it will get the song associated with the given artist.
		in_place : boolean (True)
			If True, it will not return a list, but rather modify the object to point at the first song of the obtained list.
		'''
		if self.is_song():
			titles = [self.title()]
		else:
			titles = self._disambiguate(artist=artist)
		if (len(titles)==0):
			self.__init__(self.title()+'_(song)',Itype='title')
			self.redirect()
			if self.is_song():
				titles = [self.title()]
			else:
				titles = self._disambiguate(artist=artist)
		self.redirect()
		self.find_article()
		if in_place&(len(titles)!=0):
			self.__init__(titles[0],Itype='title')
		else:
			return titles

	def _disambiguate(self,artist=None):
		title = self.title()
		dis = []
		song_titles = []
		if "(disambiguation)" not in self.title().lower():
			self.__init__(self.title()+' (disambiguation)',Itype='title')
		self.redirect()
		if ("(disambiguation)" in self.title().lower())&(self.curid()!='NA'):
			for link in get_links(self.content()):
				if song(link).is_song():
					song_titles.append(link)
			if len(song_titles) != 0:
				if artist is None:
					dis = song_titles
				else:
					a = article(artist)
					a.find_article()
					if a.curid() == "NA":
						for sep in ['and','&']:
							if sep in artist.lower():
								a = article(artist[:artist.lower().find(sep)].strip())
								a.find_article()
								break
					if a.curid() != 'NA':
						for t in song_titles:
							perf = song(t).performer()
							if perf == a.title():
								dis = [t]
		if len(dis) == 0:
			self.__init__(title,Itype='title')
		return dis

	def find_article(self):
		'''
		Find the article by trying different combinations of the title.
		'''
		self.redirect()
		if self.curid() == 'NA':
			old_title = self.title()
			titles = correct_titles(self.title())
			titles += [title+' (song)' for title in titles]
			disamb = []
			for title in titles:
				self.__init__(title,Itype='title')
				self.redirect()
				disamb.append(('(disambiguation)' in self.title()))
				if (self.curid() != 'NA')&(self.is_song()):
					break
			if self.curid() == 'NA':
				self.__init__(old_title,Itype='title')
				for i,d in enumerate(disamb):
					if d:
						self.__init__(titles[i],Itype='title')
						self.redirect()

	def is_song(self):
		if self._is_song is None:
			if self.curid()=='NA':
				self._is_song=False
			elif self._wpsong_template() is None:
				if ('song' in self._is_a().lower())|('single' in self._is_a().lower()):
					self._is_song = True
				else:
					self._is_song = False
			else:
				self._is_song = True
		return self._is_song

	def _wpsong_template(self):
		'''
		Returns the template associated to the WP Songs when available.
		'''
		if self._wpsong is None:
			self._is_song = False
			r = wp_q({'prop':"revisions",'rvprop':'content','rvsection':0,'titles':'Talk:'+self.title()})
			r = list(r['query']['pages'].values())[0]
			if 'revisions' in list(r.keys()):
				wikicode = mwparserfromhell.parse(r['revisions'][0]['*'])
				templates = wikicode.filter_templates()
				for t in templates:
					if ('songs' in t.name.lower().replace(' ','')):
						self._wpsong = t
						self._is_song = True
						break
		return self._wpsong

	def performer(self):
		return article(self.wd_prop('P175')[0]['id']).title()


class Biography(Article):
	""" Class for biographies of real people. """

	def __init__(self, I, Itype=None):
		super(Biography, self).__init__(I, Itype=None)
		self._is_bio = None
		self._wpbio = None
		self._birth_date = None
		self._death_date = None
		self._birth_place = None  # j5.place()
		self._death_place = None  # j5.place()
		self._name = None
		#if not self.is_bio():
		#	print('Warning: Not a biography ('+str(self.curid())+')')

	def __str__(self):
		self.redirect()
		out = ''
		self.title(),self.curid(),self.wdid()

		if not self.no_wp:
			out += 'curid : '+str(self.curid())+'\n'
			out += 'title : '+self.title()+'\n'
		else:
			out += 'curid : None\n'
			out += 'name  : '+self.name()+'\n' if self.name() !='NULL' else 'name  : None\n'

		if not self.no_wd:
			out += 'wdid  : '+self.wdid()+'\n'
		else:
			out += 'wdid  : None\n'

		out += 'L     : '+str(self.L())

		return out

	def name(self):
		if self._name is None:
			if self.title() is not None:
				self._name = re.sub(r'\([^\(\)]*\)','',self.title()).strip()
			else:
				data = self.data_wd()
				if 'aliases' in list(data.keys()):
					if 'en' in list(data['aliases'].keys()):
						self._name = data['aliases']['en'][0]['value']
					else:
						if len(list(data['aliases'].values()))!=0:
							self._name = list(data['aliases'].values())[0][0]['value']
						else:
							self._name = 'NULL'
				else:
					self._name = 'NULL'
		return self._name

	def desc(self):
		"""One sentence description of the person."""
		phrase,sentence,verb = self._is_a(full=True)
		ps = parse_p(sentence)
		for p in ps:
			sentence = sentence.replace(p,'')
		sentence = re.sub(r' +',' ',sentence)
		return sentence

	def age_of_meme(self, default=110):
		"""
		Returns the age of the meme defined as the number of years from the person's birthyear.
		If it is not available, it returns the default value of 110, which is the exponential of the average of the log of the age of the people in Pantheon 1, for 2019.
		"""
		today = dt.datetime.now()
		try:
			return today.year - int(self.birth_date()[0])
		except:
			return default

	def slug(self, wiki='wp', lang='en'):
		if wiki == 'wp':
			if self.title():
				if lang == 'en':
					return self.title().replace(' ', '_')
				elif lang in list(self.langlinks().keys()):
					return self.langlinks(lang).replace(' ', '_')
				else:
					return None
			else:
				return None
		elif wiki == 'wd':
			if self.no_wd:
				return None
			else:
				return self.wdid()
		else:
			return None

	def hpi(self, L=None, return_metadata=False):
		"""Calculates the Human Popularity Index."""

		np.seterr(all='raise')

		PV, PVen = self.CumulativePageviews()
		PVNE = sum(PV)
		age = self.age_of_meme()
		L_ = self.effectiveL(PV, PVen)
		CV = self.coeffOfVariation(PV, PVen)

		if not L:
			L = self.L()

		# TODO: Check error with division that's happening to 4 different profiles
		if PVNE == 0:
			PVNE = 1
		if CV == 0:
			CV = 1
		if age == 0:
			age = 1

		hpi_actual = log(L ** 2) + log(L_ ** 2) + log(age) / log(4) + log(PVNE) - log(CV)
		hpi_cutoff = log(L ** 2) + log(L_ ** 2) + log(500) / log(4) + log(PVNE) - log(CV)

		hpi = minimum(hpi_cutoff, hpi_actual)
		if hpi < 0:
			hpi = 0

		if age < 80:
			hpi -= (80 - age) / 8.

		if return_metadata:
			return L, L_, age, PVNE, CV, hpi
		else:
			return hpi

	def effectiveL(self, PV, PVen):
		H = array(PV + [PVen])
		if sum(H) == 0:
			return 1.0
		else:
			H_sum = 1 if sum(H) == 0 else sum(H)
			H = H / H_sum
			L_ = exp(entropy(H))
			return L_

	def coeffOfVariation(self, PV, PVen):
		CV = array(PV + [PVen])
		try:
			CV = std(CV) / mean(CV)
		except FloatingPointError:
			return 1
		return CV

	def gender(self):
		"""Gets the Gender of the biography."""
		genders = self.wd_prop('P21')
		if len(genders) > 0:
			gender_wdid = self.wd_prop('P21')[0]['id']
			return Article(gender_wdid).data_wd()['labels']['en']['value']
		else:
			return None

	def twitter_handle(self):
		twitter = self.wd_prop('P2002')
		if len(twitter) > 0:
			return twitter[0]['value']
		else:
			return None

	def is_bio(self):
		"""Classifier for biographies.

		Returns
		-------
		is_bio : boolean
			True if page is a biography.
		"""
		if self._is_bio is None:
			if not self.no_wp:
				if self._wpbio_template() is None:
					self._is_bio = False
				else:
					# if self._is_group():
					# 	self._is_bio = False
					# else:
					# 	self._is_bio = True
					self._is_bio = True
			else:
				self._is_bio = False

		return self._is_bio

	def _is_group(self):
		phrase, sentence, verb = self._is_a(full=True)
		if verb == 'are' or verb == 'were':
			return True
		words = set(nltk.word_tokenize(phrase.lower()))
		buzz_words = ['band', 'duo', 'group', 'team']
		for w in buzz_words:
			if w in words:
				return True
		return False

	def _wpbio_template(self):
		"""
		Returns the template associated to the WP Biography when available.
		"""
		if self._wpbio is None and self.title() is not None:
			self._is_bio = False
			r = wp_q({'prop':"revisions",'rvprop':'content','rvsection':0,'titles':'Talk:'+self.title()})
			try:
				wikicode = mwparserfromhell.parse(list(r['query']['pages'].values())[0]['revisions'][0]['*'])
				templates = wikicode.filter_templates()
				for t in templates:
					if 'biography' in t.name.lower().replace(' ','') or 'bio' in t.name.lower().replace(' ',''):
						self._wpbio = t
						self._is_bio = True
						break
			except:
				pass

		return self._wpbio

	def alive(self,boolean=False):
		"""
		Retrieves the information whether the biography is about a living or dead person.
		It uses the WikiProject Biography template from the Talk page to get this information.

		Returns
		-------
		alive : str
			Returns either 'yes' or 'no'.
		"""
		t = self._wpbio_template()
		alive = 'NULL'
		if t !='NA' and t is not None:
			for p in t.params:
				if p.name.strip().replace(' ','').lower() == 'living':
					living = drop_comments(p.value.lower().strip())
					if (living[0] == 'n'):
						alive = 'no'
						break
					elif (living[0] == 'y'):
						alive = 'yes'
						break
					else:
						alive = p.value
						break
			if alive == 'NULL':
				phrase,sentence,verb = self._is_a(full=True)
				if verb == 'is' or verb == 'are':
					alive = 'yes'
				elif verb == 'was' or verb == 'were':
					alive = 'no'
		if boolean:
			mp = defaultdict(lambda: 'NULL',{'yes':True,'no':False})
			return mp[alive]
		else:
			return alive

	def birth_date(self, raw=False):
		"""
		Gets the birth date from the infobox.
		If it is not available in the infobox (or it cannot parse it) it uses Wikidata.

		Parameters
		----------
		raw : boolean (False)
			If True it also returns the raw text from the infobox.

		Returns
		-------
		d : tuple
			(yyyy,mm,dd)
		t : string (if raw)
			Raw text from the infobox.
		"""
		if self._birth_date is None:
			d = ['NA']
			t = 'NA'

			infobox = self.infobox()

			if len(infobox) != 0:
				try:
					for box in list(infobox.values()):
						if 'birth_date' in list(box.keys()):
							t = box['birth_date']
							break

					if t != 'NA':
						d = parse_date(t)
				except:
					d = ['NA']
					t = 'NA'

			if d == ['NA'] and t == 'NA':
				t = 'wd'
				d = self.wd_prop('P569')[0]['time']
				if d != 'NA':
					if d[0]=='-':
						d = list(d.split('T')[0][1:].split('-'))
						d[0] = '-'+d[0]
						d = tuple(d)
					else:
						d = d.split('T')[0][1:].split('-')

			if d[0] == 'NA':
				t = 'wd' if t =='NA' else t
				d = self.wd_prop('P569')[0]['time']
				if d != 'NA':
					if d[0]=='-':
						d = list(d.split('T')[0][1:].split('-'))
						d[0] = '-'+d[0]
						d = tuple(d)
					else:
						d = d.split('T')[0][1:].split('-')

			self._birth_date = (d, t)

		d, t = self._birth_date

		if raw:
			return d, t
		else:
			return d

	def death_date(self, raw=False):
		"""
		Gets the death date from the infobox.
		If it is not available in the infobox (or it cannot parse it) it uses Wikidata.

		Parameters
		----------
		raw : boolean (False)
			If True it also returns the raw text from the infobox.

		Returns
		-------
		d : tuple
			(yyyy,mm,dd)
		t : string (if raw)
			Raw text from the infobox.
		"""
		if self._death_date is None:
			if self.alive() == 'yes':
				return 'alive'
			d = ['NA']
			t = 'NA'
			if len(self.infobox()) !=0:
				for box in list(self.infobox().values()):
					if 'death_date' in list(box.keys()):
						t = box['death_date']
						break
				if t != 'NA':
					d = parse_date(t)
			else:
				t = 'wd'
				d = self.wd_prop('P570')[0]['time']
				if d != 'NA':
					if d[0]=='-':
						d = list(d.split('T')[0][1:].split('-'))
						d[0] = '-'+d[0]
						d = tuple(d)
					else:
						d = d.split('T')[0][1:].split('-')
			if d[0] == 'NA':
				t = 'wd' if t =='NA' else t
				d = self.wd_prop('P570')[0]['time']
				if d != 'NA':
					if d[0]=='-':
						d = list(d.split('T')[0][1:].split('-'))
						d[0] = '-'+d[0]
						d = tuple(d)
					else:
						d = d.split('T')[0][1:].split('-')
			self._death_date = (d,t)
		d,t = self._death_date
		if raw:
			return (d,t)
		else:
			return d

	def birth_place(self):
		if self._birth_place is None:
			for box in self.infobox().values():
				if 'birth_place' in box.keys():
					for name in get_links(box[u'birth_place']):
						pl = Place(name)
						if pl.coords()[0] != 'NA':
							self._birth_place = pl
							break
					if self._birth_place is not None:
						break

		if self._birth_place is None:
			for val in self.wd_prop('P19'):
				if 'id' in val.keys():
					pl = Place(val['id'])
					if pl.coords()[0] != 'NA':
						self._birth_place = pl
						break

		return self._birth_place

	def death_place(self):
		if self._death_place is None and self.alive() == 'yes':
			self._death_place = 'alive'

		if self._death_place is None:
			for box in self.infobox().values():
				if 'death_place' in box.keys():
					for name in get_links(box[u'death_place']):
						pl = Place( name)
						if pl.coords()[0] != 'NA':
							self._death_place = pl
							break
					if self._death_place is not None:
						break

		if self._death_place is None:
			for val in self.wd_prop('P20'):
				if 'id' in val.keys():
					pl = Place(val['id'])
					if pl.coords()[0] != 'NA':
						self._death_place = pl
						break
		return self._death_place

	def occupation(self, C=None, return_all=False, override_train=False):
		"""
		Uses the occupation classifier Occ to predict the occupation.
		This function will run slow when C is not passed, since it will need to load the classifier in each call.
		Instead use:

		>>> C = johnny5.Occ()
		>>> article.occupation(C=C)

		Parameters
		----------
		C : johnny5.Occ (optional)
			Occupation classifier included in johnny5. If not provided, this function will be slow.
		return_all : Boolean (False)
			If True it will return the probabilities for all occupations in as list of 2-tuples.
		override_train : boolean (False)
			If True it will run the classifier even if the given biography belongs to the training set.

		Returns
		-------
		label : str
			Most likely occupation
		prob_ratio : float
			Ratio between the most likely occupation, and the second most likely occupation.
			If the biography belongs to the training set, it will return prob_ratio=0.
		"""
		if self._occ is None or override_train:
			if C is None:
				warnings.warn('This function will run slow because it needs to load the classifier in each call.')
			C = Occ() if C is None else C
			article = self #copy.deepcopy(self)
			self._feats = C.feats(article)
			self._occ = C.classify(article, return_all=True, override_train=override_train)

		if return_all:
			return self._occ
		else:
			if self._occ[1] == 0:
				return self._occ
			else:
				prob_ratio = self._occ[0][1]/self._occ[1][1]
				return self._occ[0][0], prob_ratio


class Band(Article):
	"""Class for music bands.

	It links to Spotify as well.
	TODO: IT SHOULD ALSO LINK TO GENIUS.
	"""

	def __init__(self,I,Itype=None):
		super(Band, self).__init__(I,Itype=None)
		self._is_band = None
		self._origin = None
		self._name = None
		self._btypes = None
		self._genres = None
		self._inception = None
		self._formation_place = None
		self._spotify_id = None
		self._top_songs = None

	def btypes(self):
		"""Categories this band is an instance of."""
		if self._btypes is None:
			tps = []
			for i in self.wd_prop('P31'):
				try:
					tps.append(Article(i['id']).title())
				except:
					pass
			self._btypes = tps
		return self._btypes

	def genres(self):
		"""Genres according to Wikidata.

		Returns
		-------
		genres : list
			List of genre names.
		"""
		if self._genres is None:
			genres = []
			for g in self.wd_prop('P136'):
				try:
					genres.append(Article(g['id']).title())
				except:
					pass
			self._genres = genres
		return self._genres

	def inception(self):
		"""Band's creation year.

		Returns
		-------
		year : int
			Formation year
		"""
		if self._inception is None:
			years = []
			for n in self.wd_prop('P571'):
				try:
					i = n['time']
					y = int(i[0]+i[1:].split('-')[0])
					cal = n['calendarmodel'].split('/')[-1]
					if cal !='Q1985727':
						warnings.warn('Unrecognized calendar type '+str(cal))
					years.append(y)
				except:
					pass
			if len(years) == 0:
				try:
					self._inception = parse_ints(self.infobox()['musical artist']['years_active'])[0]
				except:
					try:
						self._inception = parse_ints(self.infobox()['orchestra']['founded'])[0]
					except:
						self._inception = 'NULL'
			else:
				self._inception = min(years)
		return self._inception

	def formation_place(self):
		"""Gets the formation place for the band.
		Uses Wikidata and Wikipedia.

		Returns
		-------
		place_name : str
			Name of the formation place.
			Typically the title of the Wikipedia page corresponding to the place.
		country_code : str
			3-digit code of the country where the band was formed
		lat,lon : (float,float)
			Coordinates of the formation place.
		"""
		if self._formation_place is None:
			formation = []
			coords = []
			for p in self.wd_prop('P740'):
				try:
					fplace = place(p['id'])
					pname = fplace.title()
					lat,lon = fplace.coords()
					formation.append(pname)
					coords.append((lat,lon))
				except:
					pass
			ctr = []
			for c in self.wd_prop('P495'):
				try:
					ctr.append(place(c['id']).wd_prop('P298')[0]['value'])
				except:
					pass
			keep = (len(formation)!=p)
			if keep:
				keep = keep&(formation[0]!='NA')&(formation[0] is not None)
			if keep:
				lat,lon = coords[0]
				out = (formation[0],lat,lon)
			else:
				try:
					try:
						o = self.infobox()['musical artist']['origin']
					except:
						try:
							o = self.infobox()['orchestra']['origin']
						except:
							o = self.infobox()['musician']['origin']
					if '[[' in o:
						o = o[:o.find(']]')].replace('[[','').strip()
					if '|' in o:
						o = o.split('|')[0]
					if '/' in o:
						o = o.split('/')[0]
					fplace = place(o)
					fplace.find_article()
					pname = fplace.title()
					lat,lon = fplace.coords()
				except:
					pname ='NULL'
				if (pname != 'NULL')&(pname is not None):
					out = (pname,lat,lon)
				else:
					out = ('NULL','NULL','NULL')
			if len(ctr) !=0:
				self._formation_place = (out[0],ctr[0],out[1],out[2])
			else:
				self._formation_place = (out[0],'NULL',out[1],out[2])


		return self._formation_place

	def spotify_id(self):
		"""Uses Wikidata to get the spotify_id of the band.

		Returns
		-------
		spotify_id : str
			Spotify ID.
		"""
		if self._spotify_id is None:
			try:
				i = self.wd_prop('P1902')[0]['value']
			except:
				i = 'NULL'
			self._spotify_id = i
		return self._spotify_id

	def spotify_pop(self):
		"""Average popularity of the top 10 songs of the band.

		Returns
		-------
		mean(pop),max(pop),len(pop)
		"""
		if self._top_songs is None:
			if (self.spotify_id() != 'NULL')&(self.spotify_id()!='NA'):
				lz_uri = 'spotify:artist:'+self.spotify_id()
				spotify = spotipy.Spotify()
				results = spotify.artist_top_tracks(lz_uri)
				if len(results['tracks']) !=0:
					self._top_songs = results['tracks']
				else:
					self._top_songs = 'NULL'
			else:
				self._top_songs = 'NULL'
		if self._top_songs != 'NULL':
			pops = [track['popularity'] for track in self._top_songs]
			return mean(pops),max(pops),len(pops)
		else:
			return ('NULL', 'NULL', 'NULL')


class Occ:
	"""
	Occupation classifier based on Wikipedia and Wikidata information.

	Examples
	--------
	>>> C = johnny5.Occ()
	>>> b = johnny5.biography('Q937')
	>>> C.classify(b)
	"""

	def __init__(self, classifier=None):
		path = os.path.split(__file__)[0] + '/data/'

		if not classifier:
			print('Loading data from:\n' + path)
			f = open(path+'trained_classifier.pkl', 'rb')
			self._classifier = pickle.load(f, encoding='latin1')
			f.close()
		else:
			self._classifier = classifier

		self.lmt = WordNetLemmatizer()
		self.sent_detector = nltk.data.load('tokenizers/punkt/english.pickle')

		self.occ_vocab = set(open(path + 'occ_vocab.txt').read().split('\n'))
		self.tpc_vocab = set(open(path + 'tpc_vocab.txt').read().split('\n'))

		self.wdmap = defaultdict(lambda:'NA', dict([tuple(line[:-1].split('\t')) for line in open(path + "wd_occs_controlled.tsv")]))
		self.bmap  = defaultdict(lambda:'NA', dict([tuple(line[:-1].split('\t')) for line in open(path + "box_controlled.tsv")]))

		self.train = dict([tuple(line[:-1].split('\t')) for line in open(path + "train.tsv")])
		self.train_keys = set(self.train.keys())

	def classify(self, article, return_all=False, override_train=False):
		"""Classifier function.

		Parameters
		----------
		article : johnny5.biography
			Biography to classify.
		return_all : boolean (False)
			If True it will return the probabilities for all occupations in as list of 2-tuples.
		override_train : boolean (False)
			If True it will run the classifier even if the given biography belongs to the training set.

		Returns
		-------
		label : str
			Most likely occupation
		prob_ratio : float
			Ratio between the most likely occupation, and the second most likely occupation.
			If the biography belongs to the training set, it will return prob_ratio=0.
		"""
		if str(article.curid()) in self.train_keys and not override_train:
			return (self.train[str(article.curid())], 0)
		else:
			probs = self._classifier.prob_classify(self.feats(article))
			probs = sorted([(c,probs.prob(c)) for c in probs.samples()], key=operator.itemgetter(1),reverse=True)
			prob_ratio = probs[0][1]/probs[1][1]
			article._occ = probs
			if return_all:
				return probs
			else:
				return probs[0][0], prob_ratio

	def _normalize(self,text):
		text_ = text.lower()
		for word in self.occ_vocab:
			if word.replace('-',' ') in text_:
				text_ = text_.replace(word.replace('-',' '),word)
		for word in self.tpc_vocab:
			if word.replace('-',' ') in text_:
				text_ = text_.replace(word.replace('-',' '),word)
		return text_

	def _wd_occs(self,article):
		"""Returns the occupations as reported in Wikidata using the vocabulary
		provided in occ_vocab.txt.
		"""
		wd_occs = set([self.wdmap[o['id']] for o in article.wd_prop('P106')])
		if 'NA' in wd_occs:
			wd_occs.remove('NA')
		return wd_occs

	def _isa(self,article):
		"""Get the first and second occupation reported in the first sentence
		in Wikipedia, using the controlled vocabulary provided in
		box_controlled.tsv.
		"""
		ex = article.extract()
		sentences = self.sent_detector.tokenize(ex)
		first_occ = ''
		second_occ = ''
		for sentence in sentences:
			words = nltk.pos_tag(nltk.word_tokenize(sentence))
			for i,(word,tag) in enumerate(words):
				if tag[:2] == 'VB':
					if self.lmt.lemmatize(word, pos='v') == 'be':
						first_occ = 'NA'
						second_occ = 'NA'
						for ww in nltk.word_tokenize(self._normalize(str.join(' ', [w for w,t in words[i+1:]]))):
						#for ww in nltk.word_tokenize(self._normalize(' '.join([w for w,t in words[i+1:]]))):
							if (ww in self.occ_vocab):
								if (second_occ == 'NA')&(first_occ != 'NA'):
									second_occ = ww
								if (first_occ == 'NA'):
									first_occ = ww
						break
			if first_occ != '':
				return first_occ,second_occ
		return 'NA','NA'

	def _box_type(self,article):
		"""Gets the type of the first infobox of the provided Wikipedia page
		using the controlled vocabulary provided in box_controlled.tsv.
		"""
		if article.infobox() is None:
			return 'NA'
		types = [self.bmap[val.replace('_',' ').strip().replace(' ','_')] for val in list(article.infobox().keys())]
		try:
			types.remove('NA')
		except:
			pass
		if len(types) >=1:
			return types[0]
		else:
			return 'NA'

	def _topics(self,article):
		"""Gets the topic words from the Wikipedia extract of the provided
		article, using the vocabulary provided in tpc_controlled.txt.
		"""
		words = set([])
		ex = article.extract()
		ex = self._normalize(ex)
		ex_words = set(nltk.word_tokenize(ex))
		for word in self.tpc_vocab:
			if word in ex_words:
				words.add(word)
		return words

	def feats(self,article):
		"""Gets the features of the article that feed into the classifier.

		Parameters
		----------
		article : johnny5.biography
			Biography to classify.

		Returns
		-------
		features : collections.defaultdict
			Dictionary of features.
		"""
		if article._feats is None:
			feats = defaultdict(lambda:False)
			feats['btype'] = self._box_type(article)
			isa = self._isa(article)
			feats['isa1'] = isa[0]
			feats['isa2'] = isa[1]
			tpcs = self._topics(article)
			for word in tpcs:
				feats[word] = True
			wd_occs = self._wd_occs(article)
			for word in wd_occs:
				feats[word] = True
			article._feats = feats
		return article._feats


def _id_type(I):
	if _isnum(I):
		return 'curid'
	elif I.isdigit():
		return 'curid'
	elif I[0].lower() == 'q' and I[1:].isdigit():
		return 'wdid'
	else:
		return 'title'


def search(s):
	"""Searches Wikipedia and returns the first hit.

	Parameters
	----------
	s : string
		Search parameter

	Returns
	-------
	a : j5.article
		First hit of the search
	"""
	search = 'https://en.wikipedia.org/w/api.php?action=query&format=json&list=search&srsearch='+s+'&utf8='
	r = _rget(search) #.json()
	if len(r['query']['search']) != 0:
		p = r['query']['search'][0]
		return article(p['pageid'])
	else:
		return None
